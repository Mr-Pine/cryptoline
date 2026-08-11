
(*
open Ast.Cryptoline
 *)
open Common

(*
let read_typing_file file =
  let vt = Hashtbl.create 100 in
  let ch = open_in file in
  let _ =
    try
      while true do
	    let line = input_line ch in
        let tokens = List.map String.trim (String.split_on_char '=' line) in
        (match tokens with
         | v::tystr::[] ->
            let ty =
              if Str.string_match (Str.regexp "^int\\([0-9]+\\)") tystr 0 then Ast.Cryptoline.int_t (int_of_string (Str.matched_group 1 tystr))
              else if Str.string_match (Str.regexp "^sint\\([0-9]+\\)") tystr 0 then Ast.Cryptoline.int_t (int_of_string (Str.matched_group 1 tystr))
              else if Str.string_match (Str.regexp "^uint\\([0-9]+\\)") tystr 0 then Ast.Cryptoline.uint_t (int_of_string (Str.matched_group 1 tystr))
              else if tystr = "bit" then Ast.Cryptoline.bit_t
              else failwith ("Unknown type in the typing file: " ^ tystr) in
            Hashtbl.add vt v ty
         | _ -> ())
      done
    with _ ->
      () in
  let _ = close_in ch in
  vt
 *)

(*

let read_typing () =
  match !Options.Std.typing_file with
  | None -> Hashtbl.create 100
  | Some file -> read_typing_file file

let apply_auto_cast_program p =
  if !Options.Std.auto_cast then auto_cast_program ~preserve:!Options.Std.auto_cast_preserve_value p
  else p

let apply_auto_cast_spec s =
  if !Options.Std.auto_cast then { spre = s.spre; sprog = apply_auto_cast_program s.sprog; spost = s.spost; sepwss = s.sepwss; srpwss = s.srpwss }
  else s

 *)

let raise_parse_error lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let fn = if String.length curr.Lexing.pos_fname > 0 then (curr.Lexing.pos_fname ^ ":") else "" in
  let line = curr.Lexing.pos_lnum in
  let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  let tok = Lexing.lexeme lexbuf in
  let msg = Printf.sprintf "Parser error at %s(%d, %d): `%s`" fn line cnum tok in
  raise (Failure msg)

(*
 * `include "file.cl"' directives.
 *
 * A procedure can only be called or named as a case if it is defined
 * earlier in the same parse, which without this would mean assembling
 * multi-file proofs by textual concatenation -- and errors reported
 * against the concatenation's line numbers rather than anyone's file.
 * An include directive pulls the named file's procedures in instead,
 * each file parsed with its own lexbuf, so positions stay true.
 *
 * Deliberately modest semantics:
 *   - recognized only at the top of a file: among blank lines and
 *     comments, before the first procedure;
 *   - resolved relative to the file containing the directive;
 *   - each file is loaded once per parse; a repeated include is
 *     skipped (so shared dependencies are not "procedure redefined"
 *     errors, and an include cycle terminates);
 *   - the directive line is blanked rather than removed, keeping the
 *     including file's line numbers true.
 *)

let parse_include_line line =
  (* include "path" -- nothing else on the line *)
  let t = String.trim line in
  let pfx = "include" in
  if String.length t > String.length pfx && String.sub t 0 (String.length pfx) = pfx
  then
    let rest = String.trim (String.sub t (String.length pfx) (String.length t - String.length pfx)) in
    if String.length rest >= 2 && rest.[0] = '"' && rest.[String.length rest - 1] = '"'
    then Some (String.sub rest 1 (String.length rest - 2))
    else None
  else None

let comment_depth_after depth line =
  (* Track (* ... *) nesting across a line, tokenizing left to right so
     "(*)" is an opener followed by a paren, not an opener and a closer. *)
  let n = String.length line in
  let rec go i depth =
    if i + 1 >= n then depth
    else if line.[i] = '(' && line.[i + 1] = '*' then go (i + 2) (depth + 1)
    else if line.[i] = '*' && line.[i + 1] = ')' && depth > 0 then go (i + 2) (depth - 1)
    else go (i + 1) depth
  in
  go 0 depth

let scan_includes text =
  (* Returns the directives from the top of the file, and the text with
     each directive line blanked. *)
  let lines = String.split_on_char '\n' text in
  let rec go depth acc kept = function
    | [] -> (List.rev acc, List.rev kept)
    | line :: rest ->
       if depth > 0 then go (comment_depth_after depth line) acc (line :: kept) rest
       else if String.trim line = "" then go depth acc (line :: kept) rest
       else match parse_include_line line with
            | Some path -> go depth (path :: acc) ("" :: kept) rest
            | None ->
               let depth' = comment_depth_after depth line in
               if depth' > depth || String.length (String.trim line) >= 2
                  && String.sub (String.trim line) 0 2 = "(*"
               then go depth' acc (line :: kept) rest
               else (List.rev acc, List.rev kept @ (line :: rest))
  in
  let (incs, kept) = go 0 [] [] lines in
  (incs, String.concat "\n" kept)

let read_file file =
  let ic = open_in_bin file in
  let text = really_input_string ic (in_channel_length ic) in
  let _ = close_in ic in
  text

let procs_from_lexbuf lexbuf =
  try
    CryptolineParser.procs_only CryptolineLexer.token lexbuf
  with
  | Failure msg -> raise (Failure ("Error at line " ^ string_of_int (get_line_start()) ^ ". " ^ msg))
  | Parsing.Parse_error -> raise_parse_error lexbuf

let rec load_procs seen file =
  let key = (* light normalization; include-once is by resolved path text *)
    let f = file in
    if String.length f > 2 && String.sub f 0 2 = "./" then String.sub f 2 (String.length f - 2) else f in
  if Hashtbl.mem seen key then []
  else
    let _ = Hashtbl.add seen key () in
    let text = read_file file in
    let (incs, blanked) = scan_includes text in
    let resolve p =
      let r = if Filename.is_relative p then Filename.concat (Filename.dirname file) p else p in
      if Sys.file_exists r then r
      else raise (Failure (Printf.sprintf "include \"%s\" in %s: no such file" p file)) in
    let pre = List.concat_map (fun p -> load_procs seen (resolve p)) incs in
    let lexbuf = Lexing.from_string ~with_positions:true blanked in
    let _ = Lexing.set_filename lexbuf file in
    pre @ [procs_from_lexbuf lexbuf]

let procs_tok_of_file file =
  let toks = load_procs (Hashtbl.create 7) file in
  fun ctx -> List.iter (fun t -> t ctx) toks

let specs_from_file file =
  Common.parse_specs (procs_tok_of_file file)



let spec_from_lexbuf lexbuf =
  try
    CryptolineParser.spec CryptolineLexer.token lexbuf
  with
  | Failure msg -> raise (Failure ("Error at line " ^ string_of_int (get_line_start()) ^ ". " ^ msg))
  | Parsing.Parse_error -> raise_parse_error lexbuf

let spec_from_file file =
  Common.parse_spec (procs_tok_of_file file)

let spec_from_string str =
  spec_from_lexbuf (Lexing.from_string ~with_positions:true str)

let program_from_lexbuf lexbuf =
  try
    CryptolineParser.prog CryptolineLexer.token lexbuf
  with
  | Failure msg -> raise (Failure ("Error at line " ^ string_of_int (get_line_start()) ^ ". " ^ msg))
  | Parsing.Parse_error -> raise_parse_error lexbuf

let program_from_file file =
  let lexbuf = Lexing.from_channel (open_in file) in
  let _ = Lexing.set_filename lexbuf file in
  program_from_lexbuf lexbuf

let program_from_string str =
  program_from_lexbuf (Lexing.from_string str)

let espec_from_lexbuf lexbuf =
  try
    SpecParser.espec SpecLexer.token lexbuf
  with
  | Failure msg -> raise (Failure msg)
  | Parsing.Parse_error -> raise_parse_error lexbuf

let espec_from_file file =
  let lexbuf = Lexing.from_channel (open_in file) in
  let _ = Lexing.set_filename lexbuf file in
  espec_from_lexbuf lexbuf

let espec_from_string str =
  espec_from_lexbuf (Lexing.from_string str)

let rspec_from_lexbuf lexbuf =
  try
    SpecParser.rspec SpecLexer.token lexbuf
  with
  | Failure msg -> raise (Failure msg)
  | Parsing.Parse_error -> raise_parse_error lexbuf

let rspec_from_file file =
  let lexbuf = Lexing.from_channel (open_in file) in
  let _ = Lexing.set_filename lexbuf file in
  rspec_from_lexbuf lexbuf

let rspec_from_string str =
  rspec_from_lexbuf (Lexing.from_string str)
