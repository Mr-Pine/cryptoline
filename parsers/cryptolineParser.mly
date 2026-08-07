%{

(*
 * Use raise_at_line or raise_at to raise an exception if the error location
 * can be determined. Raise ParseError otherwise.
 *)

  open Ast.Cryptoline
  open Ast.MultiTrack
  open Common

%}

%token <string> COMMENT
%token <Z.t> NUM
%token <string> ID VEC_ID PATH
%token <int> UINT SINT
%token BIT
%token LBRAC RBRAC LPAR RPAR LSQUARE RSQUARE COMMA SEMICOLON DOT DOTDOT VBAR COLON
/* Instructions */
%token CONST MOV EXTRACT
%token BROADCAST
%token ADD ADDS ADC ADCS SUB SUBC SUBB SBC SBCS SBB SBBS MUL MULS MULL MULJ UDIV SDIV SPLIT SPL
%token UADD UADDS UADC UADCS USUB USUBC USUBB USBC USBCS USBB USBBS UMUL UMULS UMULL UMULJ USPLIT USPL
%token SADD SADDS SADC SADCS SSUB SSUBC SSUBB SSBC SSBCS SSBB SSBBS SMUL SMULS SMULL SMULJ SSPLIT SSPL
%token SHL SHLS SHR SHRS SAR SARS CSHL CSHLS CSHR CSHRS ROL ROR CONCAT SET CLEAR NONDET CMOV AND OR NOT CAST VPC JOIN ASSERT EASSERT RASSERT ASSUME SMT2CAS GHOST
%token CUT ECUT RCUT NOP SETEQ SETNE CASE ELSE REPEAT
/* Logical Expressions */
%token VARS NEG SQ EXT UEXT SEXT MOD UMOD SREM SMOD XOR ULT ULE UGT UGE SLT SLE SGT SGE SHR SAR
/* Predicates */
%token TRUE EQ EQMOD EQUMOD EQSMOD EQSREM
/* Operators */
%token ADDOP SUBOP MULOP POWOP ULEOP ULTOP UGEOP UGTOP SLEOP SLTOP SGEOP SGTOP EQOP NEGOP MODOP LANDOP LOROP NOTOP ANDOP OROP XOROP SHLOP SHROP SAROP ADDADDOP
/* Others */
%token AT PROC INLINE INLINESPEC CALL ULIMBS SLIMBS POLY PROVE WITH ALL CUTS ASSUMES GHOSTS PRECONDITION DEREFOP ALGEBRA RANGE QFBV SOLVER SMT LIA NIA
%token EOF DOLPHIN
%token BOGUS

%left LOROP
%left LANDOP
%nonassoc EQOP ULTOP ULEOP UGTOP UGEOP SLTOP SLEOP SGTOP SGEOP
%left OROP
%left XOROP
%left ANDOP
%left SHLOP SHROP SAROP
%left ADDOP SUBOP ADDADDOP
%left MULOP
%left POWOP
%right NEGOP NOTOP
%left MODOP
%nonassoc VAR CONST NEG ADD SUB MUL SQ UMOD SREM SMOD NOT AND OR XOR ULT ULE UGT UGE SLT SLE SGT SGE SHL SHLS SHR SHRS SAR SARS ROL ROR CONCAT
%nonassoc SETEQ SETNE EQ EQMOD
%nonassoc UMINUS DOLPHIN

%start specs
%start spec
%start prog
%type <((Ast.Cryptoline.var list * Ast.Cryptoline.var list) * Typecheck.Std.tagged_spec) Ast.Cryptoline.SM.t> specs
%type <(Ast.Cryptoline.var list * Typecheck.Std.tagged_spec)> spec
%type <Ast.MultiTrack.lined_tagged_program> prog

%type <lval_t> lval
%type <lval_vec_t> lval_v
%type <atom_t> atom
%type <unit> opt_comma
%type <atom_vec_t> atom_v

%%

specs:
  procs EOF                                       { parse_specs $1 }
;

spec:
  procs EOF                                       { parse_spec $1 }
;

procs:
    proc procs                                    { fun ctx -> $1 ctx; $2 ctx }
  |                                               { fun _ -> () }
;

proc:
    PROC ID LPAR formals RPAR EQOP pre program post
                                                  { parse_proc (get_line_start()) $2 $4 $7 $8 $9 }
  | CONST ID EQOP eexp const_stmt_suffix          { parse_global_constant (get_line_start()) $2 $4 }
;

const_stmt_suffix:
              {}
  | SEMICOLON {}
;

pre:
    LBRAC tagged_bexp RBRAC                       { fun ctx -> Some ($2 ctx) }
  |                                               { fun _ -> None }
;

post:
    LBRAC tagged_bexp_prove_with_list RBRAC       { fun ctx -> Some ($2 ctx) }
  |                                               { fun _ -> None }
;

formals:
    fvars                                         { ($1, []) }
  | fvars SEMICOLON fvars                         { ($1, $3) }
  | SEMICOLON fvars                               { ([], $2) }
  |                                               { ([], []) }
;

fvars:
    fvar                                          { $1 }
  | fvar COMMA fvars                              { parse_fvar_cons (get_line_start()) $1 $3 }
;

fvar:
    fvar_primary                                  { $1 }
  | fvar_vec                                      { $1 }
;

fvar_primary:
    typ ID                                        { parse_fvar (get_line_start()) $2 $1 }
  | ID AT typ                                     { parse_fvar (get_line_start()) $1 $3 }
  | typ ID OROP NUM DOTDOT NUM                    { parse_fvar_expansion (get_line_start()) $2 $1 $4 $6 }
  | ID AT typ OROP NUM DOTDOT NUM                 { parse_fvar_expansion (get_line_start()) $1 $3 $5 $7 }
;

fvar_vec:
    vectyp VEC_ID                                 { parse_fvar_vec (get_line_start()) $2 $1 }
  | VEC_ID AT vectyp                              { parse_fvar_vec (get_line_start()) $1 $3 }
;

prog:
  program EOF
    {
      parse_instrs (empty_parsing_context ()) $1
    }
;

program:
  instrs                                          { $1 }
;

instrs:
    instr SEMICOLON                               { [$1] }
  | instr SEMICOLON instrs                        { $1 :: $3 }
  | instr instr                                   { raise_at (get_rhs_end 1) ("A semicolon is expected at the end of an instruction.") }
;

instr:
    MOV lval opt_comma atom                       { (get_line_start(), `MOV ($2, $4)) }
  | MOV lval_v_nonbare opt_comma atom_v           { (get_line_start(), `VMOV ($2, $4)) }
/* A bare vector name followed by a bracket is either a destination indexed by
   what is in the bracket, which a comma then separates from the source, or a
   whole vector destination whose source is the bracketed literal. Parse the
   bracket once and let the comma tell the two apart. Everywhere else the
   destination ends in a way that leaves no doubt. */
  | MOV VEC_ID atom_v_nolit                       { (get_line_start(), `VMOV (`LVVECT { vecname = $2; vectyphint = None }, $3)) }
  | MOV VEC_ID COMMA atom_v                       { (get_line_start(), `VMOV (`LVVECT { vecname = $2; vectyphint = None }, $4)) }
  | MOV VEC_ID LSQUARE atom_scalars RSQUARE       { (get_line_start(), `VMOV (`LVVECT { vecname = $2; vectyphint = None }, `AVLIT $4)) }
  | MOV VEC_ID LSQUARE atom_scalars RSQUARE COMMA atom
                                                  { (get_line_start(), `MOVELM ($2, $4, $7)) }
  | EXTRACT lval_v LSQUARE nums RSQUARE atom_vs   { (get_line_start(), `EXTRACT ($2, $4, $6)) }
  | lval EQOP atom                                { (get_line_start(), `MOV ($1, $3)) }
  | BROADCAST lval_v opt_comma const_exp_primary opt_comma atom_v { (get_line_start(), `VBROADCAST ($2, $4, $6)) }
  | SHL lval opt_comma atom opt_comma atom        { (get_line_start(), `SHL ($2, $4, $6)) }
  | SHL lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSHL ($2, $4, $6)) }
  | lval EQOP SHL atom opt_comma atom             { (get_line_start(), `SHL ($1, $4, $6)) }
  | SHLS lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `SHLS ($2, $4, $6, $8)) }
  | SHLS lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_v_primary { (get_line_start(), `VSHLS ($2, $4, $6, $8)) }
  | lval opt_comma lval EQOP SHLS atom opt_comma const_exp_primary { (get_line_start(), `SHLS ($1, $3, $6, $8)) }
  | SHR lval opt_comma atom opt_comma atom        { (get_line_start(), `SHR ($2, $4, $6)) }
  | SHR lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSHR ($2, $4, $6)) }
  | lval EQOP SHR atom opt_comma atom             { (get_line_start(), `SHR ($1, $4, $6)) }
  | SHRS lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `SHRS ($2, $4, $6, $8)) }
  | SHRS lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_v_primary { (get_line_start(), `VSHRS ($2, $4, $6, $8)) }
  | lval opt_comma lval EQOP SHRS atom opt_comma const_exp_primary { (get_line_start(), `SHRS ($1, $3, $6, $8)) }
  | SAR lval opt_comma atom opt_comma atom        { (get_line_start(), `SAR ($2, $4, $6)) }
  | SAR lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSAR ($2, $4, $6)) }
  | lval EQOP SAR atom opt_comma atom             { (get_line_start(), `SAR ($1, $4, $6)) }
  | SARS lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `SARS ($2, $4, $6, $8)) }
  | SARS lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_v_primary { (get_line_start(), `VSARS ($2, $4, $6, $8)) }
  | lval opt_comma lval EQOP SARS atom opt_comma const_exp_primary { (get_line_start(), `SARS ($1, $3, $6, $8)) }
  | CSHL lval opt_comma lval opt_comma atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHL ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP CSHL atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHL ($1, $3, $6, $8, $10)) }
  | CSHLS lval opt_comma lval opt_comma lval opt_comma atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHLS ($2, $4, $6, $8, $10, $12)) }
  | lval DOT lval DOT lval EQOP CSHLS atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHLS ($1, $3, $5, $8, $10, $12)) }
  | CSHR lval opt_comma lval opt_comma atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHR ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP CSHR atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHR ($1, $3, $6, $8, $10)) }
  | CSHRS lval opt_comma lval opt_comma lval opt_comma atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHRS ($2, $4, $6, $8, $10, $12)) }
  | lval DOT lval DOT lval EQOP CSHRS atom opt_comma atom opt_comma const_exp_primary { (get_line_start(), `CSHRS ($1, $3, $5, $8, $10, $12)) }
  | ROL lval opt_comma atom opt_comma atom        { (get_line_start(), `ROL ($2, $4, $6)) }
  | ROL lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VROL ($2, $4, $6)) }
  | ROR lval opt_comma atom opt_comma atom        { (get_line_start(), `ROR ($2, $4, $6)) }
  | ROR lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VROR ($2, $4, $6)) }
  | SET lval                                      { (get_line_start(), `SET $2) }
  | SET lval_v                                    { (get_line_start(), `VSET $2) }
  | CLEAR lval                                    { (get_line_start(), `CLEAR $2) }
  | CLEAR lval_v                                  { (get_line_start(), `VCLEAR $2) }
  | NONDET lval                                   { (get_line_start(), `NONDET $2) }
  | NONDET lval_v                                 { (get_line_start(), `VNONDET $2) }
  | CMOV lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `CMOV ($2, $4, $6, $8)) }
  | CMOV lval_v opt_comma atom_v_primary opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VCMOV ($2, $4, $6, $8)) }
  | lval EQOP CMOV atom opt_comma atom opt_comma atom { (get_line_start(), `CMOV ($1, $4, $6, $8)) }
  | ADD lval opt_comma atom opt_comma atom        { (get_line_start(), `ADD ($2, $4, $6)) }
  | ADD lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VADD ($2, $4, $6)) }
  | lval EQOP ADD atom opt_comma atom             { (get_line_start(), `ADD ($1, $4, $6)) }
  | ADDS lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `ADDS ($2, $4, $6, $8)) }
  | ADDS lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VADDS ($2, $4, $6, $8)) }
  | lval DOT lval EQOP ADDS atom opt_comma atom   { (get_line_start(), `ADDS ($1,  $3, $6, $8)) }
  | ADC lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `ADC ($2, $4, $6, $8)) }
  | lval EQOP ADC atom opt_comma atom opt_comma atom { (get_line_start(), `ADC ($1, $4, $6, $8)) }
  | ADCS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `ADCS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP ADCS atom opt_comma atom opt_comma atom { (get_line_start(), `ADCS ($1, $3, $6, $8, $10)) }
  | SUB lval opt_comma atom opt_comma atom        { (get_line_start(), `SUB ($2, $4, $6)) }
  | SUB lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSUB ($2, $4, $6)) }
  | lval EQOP SUB atom opt_comma atom             { (get_line_start(), `SUB ($1, $4, $6)) }
  | SUBC lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `SUBC ($2, $4, $6, $8)) }
  | SUBC lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSUBC ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SUBC atom opt_comma atom   { (get_line_start(), `SUBC ($1, $3, $6, $8)) }
  | SUBB lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `SUBB ($2, $4, $6, $8)) }
  | SUBB lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSUBB ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SUBB atom opt_comma atom   { (get_line_start(), `SUBB ($1, $3, $6, $8)) }
  | SBC lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SBC ($2, $4, $6, $8)) }
  | lval EQOP SBC atom opt_comma atom opt_comma atom { (get_line_start(), `SBC ($1, $4, $6, $8)) }
  | SBCS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SBCS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP SBCS atom opt_comma atom opt_comma atom { (get_line_start(), `SBCS ($1, $3, $6, $8, $10)) }
  | SBB lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SBB ($2, $4, $6, $8)) }
  | lval EQOP SBB atom opt_comma atom opt_comma atom { (get_line_start(), `SBB ($1, $4, $6, $8)) }
  | SBBS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SBBS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP SBBS atom opt_comma atom opt_comma atom { (get_line_start(), `SBBS ($1, $3, $6, $8, $10)) }
  | MUL lval opt_comma atom opt_comma atom        { (get_line_start(), `MUL ($2, $4, $6)) }
  | MUL lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VMUL ($2, $4, $6)) }
  | lval EQOP MUL atom opt_comma atom             { (get_line_start(), `MUL ($1, $4, $6)) }
  | MULS lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `MULS ($2, $4, $6, $8)) }
  | lval DOT lval EQOP MULS atom opt_comma atom   { (get_line_start(), `MULS ($1, $3, $6, $8)) }
  | MULL lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `MULL ($2, $4, $6, $8)) }
  | MULL lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VMULL ($2, $4, $6, $8)) }
  | lval DOT lval EQOP MULL atom opt_comma atom   { (get_line_start(), `MULL ($1, $3, $6, $8)) }
  | MULJ lval opt_comma atom opt_comma atom       { (get_line_start(), `MULJ ($2, $4, $6)) }
  | MULJ lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VMULJ ($2, $4, $6)) }
  | lval EQOP MULJ atom opt_comma atom            { (get_line_start(), `MULJ ($1, $4, $6)) }
  | SPLIT lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `SPLIT ($2, $4, $6, $8)) }
  | SPLIT lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_primary { (get_line_start(), `VSPLIT ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SPLIT atom opt_comma const_exp_primary { (get_line_start(), `SPLIT ($1, $3, $6, $8)) }
  | SPL lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `SPL ($2, $4, $6, $8)) }
  | SPL lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_primary { (get_line_start(), `VSPL ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SPL atom opt_comma const_exp_primary { (get_line_start(), `SPL ($1, $3, $6, $8)) }
  | SETEQ lval opt_comma atom opt_comma atom      { (get_line_start(), `SETEQ ($2, $4, $6)) }
  | SETEQ lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSETEQ ($2, $4, $6)) }
  | SETNE lval opt_comma atom opt_comma atom      { (get_line_start(), `SETNE ($2, $4, $6)) }
  | SETNE lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSETNE ($2, $4, $6)) }
  | UADD lval opt_comma atom opt_comma atom       { (get_line_start(), `UADD ($2, $4, $6)) }
  | UADD lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VUADD ($2, $4, $6)) }
  | lval EQOP UADD atom opt_comma atom            { (get_line_start(), `UADD ($1, $4, $6)) }
  | UADDS lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `UADDS ($2, $4, $6, $8)) }
  | UADDS lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VUADDS ($2, $4, $6, $8)) }
  | lval DOT lval EQOP UADDS atom opt_comma atom  { (get_line_start(), `UADDS ($1, $3, $6, $8)) }
  | UADC lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `UADC ($2, $4, $6, $8)) }
  | lval EQOP UADC atom opt_comma atom opt_comma atom { (get_line_start(), `UADC ($1, $4, $6, $8)) }
  | UADCS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `UADCS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP UADCS atom opt_comma atom opt_comma atom { (get_line_start(), `UADCS ($1, $3, $6, $8, $10)) }
  | USUB lval opt_comma atom opt_comma atom       { (get_line_start(), `USUB ($2, $4, $6)) }
  | lval EQOP USUB atom opt_comma atom            { (get_line_start(), `USUB ($1, $4, $6)) }
  | USUBC lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `USUBC ($2, $4, $6, $8)) }
  | lval DOT lval EQOP USUBC atom opt_comma atom  { (get_line_start(), `USUBC ($1, $3, $6, $8)) }
  | USUBB lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `USUBB ($2, $4, $6, $8)) }
  | lval DOT lval EQOP USUBB atom opt_comma atom  { (get_line_start(), `USUBB ($1, $3, $6, $8)) }
  | USBC lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `USBC ($2, $4, $6, $8)) }
  | lval EQOP USBC atom opt_comma atom opt_comma atom { (get_line_start(), `USBC ($1, $4, $6, $8)) }
  | USBCS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `USBCS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP USBCS atom opt_comma atom opt_comma atom { (get_line_start(), `USBCS ($1, $3, $6, $8, $10)) }
  | USBB lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `USBB ($2, $4, $6, $8)) }
  | lval EQOP USBB atom opt_comma atom opt_comma atom { (get_line_start(), `USBB ($1, $4, $6, $8)) }
  | USBBS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `USBBS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP USBBS atom opt_comma atom opt_comma atom { (get_line_start(), `USBBS ($1, $3, $6, $8, $10)) }
  | UMUL lval opt_comma atom opt_comma atom       { (get_line_start(), `UMUL ($2, $4, $6)) }
  | UMUL lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VUMUL ($2, $4, $6)) }
  | lval EQOP UMUL atom opt_comma atom            { (get_line_start(), `UMUL ($1, $4, $6)) }
  | UMULS lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `UMULS ($2, $4, $6, $8)) }
  | lval DOT lval EQOP UMULS atom opt_comma atom  { (get_line_start(), `UMULS ($1, $3, $6, $8)) }
  | UMULL lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `UMULL ($2, $4, $6, $8)) }
  | UMULL lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VUMULL ($2, $4, $6, $8)) }
  | lval DOT lval EQOP UMULL atom opt_comma atom  { (get_line_start(), `UMULL ($1, $3, $6, $8)) }
  | UMULJ lval opt_comma atom opt_comma atom      { (get_line_start(), `UMULJ ($2, $4, $6)) }
  | UMULJ lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VUMULJ ($2, $4, $6)) }
  | lval EQOP UMULJ atom opt_comma atom           { (get_line_start(), `UMULJ ($1, $4, $6)) }
  | USPLIT lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `USPLIT ($2, $4, $6, $8)) }
  | USPLIT lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_primary { (get_line_start(), `VUSPLIT ($2, $4, $6, $8)) }
  | lval DOT lval EQOP USPLIT atom opt_comma const_exp_primary { (get_line_start(), `USPLIT ($1, $3, $6, $8)) }
  | USPL lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `USPL ($2, $4, $6, $8)) }
  | USPL lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_primary { (get_line_start(), `VUSPL ($2, $4, $6, $8)) }
  | lval DOT lval EQOP USPL atom opt_comma const_exp_primary { (get_line_start(), `USPL ($1, $3, $6, $8)) }
  | SADD lval opt_comma atom opt_comma atom       { (get_line_start(), `SADD ($2, $4, $6)) }
  | SADD lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSADD ($2, $4, $6)) }
  | lval EQOP SADD atom opt_comma atom            { (get_line_start(), `SADD ($1, $4, $6)) }
  | SADDS lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `SADDS ($2, $4, $6, $8)) }
  | SADDS lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSADDS ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SADDS atom opt_comma atom  { (get_line_start(), `SADDS ($1, $3, $6, $8)) }
  | SADC lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SADC ($2, $4, $6, $8)) }
  | lval EQOP SADC atom opt_comma atom opt_comma atom { (get_line_start(), `SADC ($1, $4, $6, $8)) }
  | SADCS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SADCS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP SADCS atom opt_comma atom opt_comma atom { (get_line_start(), `SADCS ($1, $3, $6, $8, $10)) }
  | SSUB lval opt_comma atom opt_comma atom       { (get_line_start(), `SSUB ($2, $4, $6)) }
  | lval EQOP SSUB atom opt_comma atom            { (get_line_start(), `SSUB ($1, $4, $6)) }
  | SSUBC lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `SSUBC ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SSUBC atom opt_comma atom  { (get_line_start(), `SSUBC ($1, $3, $6, $8)) }
  | SSUBB lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `SSUBB ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SSUBB atom opt_comma atom  { (get_line_start(), `SSUBB ($1, $3, $6, $8)) }
  | SSBC lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SSBC ($2, $4, $6, $8)) }
  | lval EQOP SSBC atom opt_comma atom opt_comma atom { (get_line_start(), `SSBC ($1, $4, $6, $8)) }
  | SSBCS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SSBCS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP SSBCS atom opt_comma atom opt_comma atom { (get_line_start(), `SSBCS ($1, $3, $6, $8, $10)) }
  | SSBB lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SSBB ($2, $4, $6, $8)) }
  | lval EQOP SSBB atom opt_comma atom opt_comma atom { (get_line_start(), `SSBB ($1, $4, $6, $8)) }
  | SSBBS lval opt_comma lval opt_comma atom opt_comma atom opt_comma atom { (get_line_start(), `SSBBS ($2, $4, $6, $8, $10)) }
  | lval DOT lval EQOP SSBBS atom opt_comma atom opt_comma atom { (get_line_start(), `SSBBS ($1, $3, $6, $8, $10)) }
  | SMUL lval opt_comma atom opt_comma atom       { (get_line_start(), `SMUL ($2, $4, $6) )}
  | SMUL lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSMUL ($2, $4, $6) )}
  | lval EQOP SMUL atom opt_comma atom            { (get_line_start(), `SMUL ($1, $4, $6) )}
  | SMULS lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `SMULS ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SMULS atom opt_comma atom  { (get_line_start(), `SMULS ($1, $3, $6, $8)) }
  | SMULL lval opt_comma lval opt_comma atom opt_comma atom { (get_line_start(), `SMULL ($2, $4, $6, $8)) }
  | SMULL lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSMULL ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SMULL atom opt_comma atom  { (get_line_start(), `SMULL ($1, $3, $6, $8)) }
  | SMULJ lval opt_comma atom opt_comma atom      { (get_line_start(), `SMULJ ($2, $4, $6)) }
  | SMULJ lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VSMULJ ($2, $4, $6)) }
  | lval EQOP SMULJ atom opt_comma atom           { (get_line_start(), `SMULJ ($1, $4, $6)) }
  | SSPLIT lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `SSPLIT ($2, $4, $6, $8)) }
  | SSPLIT lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_primary { (get_line_start(), `VSSPLIT ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SSPLIT atom opt_comma const_exp_primary { (get_line_start(), `SSPLIT ($1, $3, $6, $8)) }
  | SSPL lval opt_comma lval opt_comma atom opt_comma const_exp_primary { (get_line_start(), `SSPL ($2, $4, $6, $8)) }
  | SSPL lval_v opt_comma lval_v opt_comma atom_v_primary opt_comma const_exp_primary { (get_line_start(), `VSSPL ($2, $4, $6, $8)) }
  | lval DOT lval EQOP SSPL atom opt_comma const_exp_primary { (get_line_start(), `SSPL ($1, $3, $6, $8)) }
  | AND lval opt_comma atom opt_comma atom        { (get_line_start(), `AND ($2, $4, $6)) }
  | AND lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VAND ($2, $4, $6)) }
  | lval EQOP AND atom opt_comma atom             { (get_line_start(), `AND ($1, $4, $6)) }
  | OR lval opt_comma atom opt_comma atom         { (get_line_start(), `OR ($2, $4, $6)) }
  | OR lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VOR ($2, $4, $6)) }
  | lval EQOP OR atom opt_comma atom              { (get_line_start(), `OR ($1, $4, $6)) }
  | XOR lval opt_comma atom opt_comma atom        { (get_line_start(), `XOR ($2, $4, $6)) }
  | XOR lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VXOR ($2, $4, $6)) }
  | lval EQOP XOR atom opt_comma atom             { (get_line_start(), `XOR ($1, $4, $6)) }
  | NOT lval opt_comma atom                       { (get_line_start(), `NOT ($2, $4)) }
  | NOT lval_v opt_comma atom_v_primary           { (get_line_start(), `VNOT ($2, $4)) }
  | lval EQOP NOT atom                            { (get_line_start(), `NOT ($1, $4)) }
  | CAST lval opt_comma atom                      { (get_line_start(), `CAST (None, $2, $4)) }
  | CAST lval_v opt_comma atom_v_primary          { (get_line_start(), `VCAST (None, $2, $4)) }
  // XXX: the "[]" is to workaround a r/r conflict (TODO: remove this rule as the conflict has been resolved)
  | CAST LSQUARE RSQUARE lval_v opt_comma atom_v_primary { (get_line_start(), `VCAST (None, $4, $6)) }
  /* Only one lval is expected in lval_scalars */
  | CAST LSQUARE lval_scalars RSQUARE lval opt_comma atom { match $3 with
                                                    | [] -> (get_line_start(), `CAST (None, $5, $7))
                                                    | lv::[] -> (get_line_start(), `CAST (Some lv, $5, $7))
                                                    | _ -> failwith "" }
  | lval EQOP CAST atom                           { (get_line_start(), `CAST (None, $1, $4)) }
  | VPC lval opt_comma atom                       { (get_line_start(), `VPC ($2, $4)) }
  | VPC lval_v opt_comma atom_v_primary           { (get_line_start(), `VVPC ($2, $4)) }
  // XXX: the "[]" is to workaround a r/r conflict (TODO: remove this rule as the conflict has been resolved)
  | VPC LSQUARE RSQUARE lval_v opt_comma atom_v_primary { (get_line_start(), `VVPC ($4, $6)) }
  | lval EQOP VPC atom                            { (get_line_start(), `VPC ($1, $4)) }
  | JOIN lval opt_comma atom opt_comma atom       { (get_line_start(), `JOIN ($2, $4, $6)) }
  | lval EQOP JOIN atom opt_comma atom            { (get_line_start(), `JOIN ($1, $4, $6)) }
  | JOIN lval_v opt_comma atom_v_primary opt_comma atom_v_primary { (get_line_start(), `VJOIN ($2, $4, $6)) }
/*
  | ASSERT bexp_prove_with_list                   { (get_line_start(), `ASSERT $2) }
  | EASSERT ebexp_prove_with_list                 { (get_line_start(), `EASSERT $2) }
  | RASSERT rbexp_prove_with_list                 { (get_line_start(), `RASSERT $2) }
  | ASSUME bexp                                   { (get_line_start(), `ASSUME $2) }
  | CUT bexp_prove_with_list                      { (get_line_start(), `CUT $2) }
  | ECUT ebexp_prove_with_list                    { (get_line_start(), `ECUT $2) }
  | RCUT rbexp_prove_with_list                    { (get_line_start(), `RCUT $2) }
  | GHOST gvars COLON bexp                        { (get_line_start(), `GHOST ($2, $4)) }
*/
  | ASSERT tagged_bexp_prove_with_list            { (get_line_start(), `TASSERT $2) }
  | EASSERT tagged_ebexp_prove_with_list          { (get_line_start(), `TEASSERT $2) }
  | RASSERT tagged_rbexp_prove_with_list          { (get_line_start(), `TRASSERT $2) }
  | ASSUME tagged_bexp                            { (get_line_start(), `TASSUME $2) }
  | SMT2CAS tagged_rbexp_prove_with_list          { (get_line_start(), `TSMT2CAS $2) }
  | CUT tagged_bexp_prove_with_list               { (get_line_start(), `TCUT $2) }
  | ECUT tagged_ebexp_prove_with_list             { (get_line_start(), `TECUT $2) }
  | RCUT tagged_rbexp_prove_with_list             { (get_line_start(), `TRCUT $2) }
  | GHOST gvars COLON tagged_bexp                 { (get_line_start(), `TGHOST ($2, $4)) }
  /* Extensions */
  | CALL ID LPAR actuals RPAR                     { (get_line_start(), `CALL ($2, $4)) }
  | INLINESPEC ID LPAR actuals RPAR               { (get_line_start(), `INLINESPEC ($2, $4)) }
  | INLINE ID LPAR actuals RPAR                   { (get_line_start(), `INLINE ($2, $4)) }
  | NOP                                           { (get_line_start(), `NOP) }
  | CASE ID EQOP atom LSQUARE case_values RSQUARE LBRAC case_body RBRAC { (get_line_start(), `CASE ($2, $4, $6, $9, None)) }
  | CASE ID EQOP atom LSQUARE case_values RSQUARE LBRAC case_body RBRAC ELSE LBRAC case_body RBRAC { (get_line_start(), `CASE ($2, $4, $6, $9, Some $13)) }
  | REPEAT ID EQOP LSQUARE case_values RSQUARE LBRAC case_body RBRAC { (get_line_start(), `REPEAT ($2, $5, $8)) }
  /* Errors */
  | MOV error                                     { raise_at_line (get_line_start()) ("Bad mov instruction") }
  | BROADCAST error                               { raise_at_line (get_line_start()) ("Bad broadcast instruction") }
  | ADD error                                     { raise_at_line (get_line_start()) ("Bad add instruction") }
  | ADDS error                                    { raise_at_line (get_line_start()) ("Bad adds instruction") }
  | ADC error                                     { raise_at_line (get_line_start()) ("Bad adc instruction") }
  | ADCS error                                    { raise_at_line (get_line_start()) ("Bad adcs instruction") }
  | SUB error                                     { raise_at_line (get_line_start()) ("Bad sub instruction") }
  | SUBC error                                    { raise_at_line (get_line_start()) ("Bad subc instruction") }
  | SUBB error                                    { raise_at_line (get_line_start()) ("Bad subb instruction") }
  | SBC error                                     { raise_at_line (get_line_start()) ("Bad sbc instruction") }
  | SBCS error                                    { raise_at_line (get_line_start()) ("Bad sbcs instruction") }
  | SBB error                                     { raise_at_line (get_line_start()) ("Bad sbb instruction") }
  | SBBS error                                    { raise_at_line (get_line_start()) ("Bad sbbs instruction") }
  | MUL error                                     { raise_at_line (get_line_start()) ("Bad mul instruction") }
  | MULL error                                    { raise_at_line (get_line_start()) ("Bad mull instruction") }
  | SPLIT error                                   { raise_at_line (get_line_start()) ("Bad split instruction") }
  | SPL error                                     { raise_at_line (get_line_start()) ("Bad spl instruction") }
  | UADD error                                    { raise_at_line (get_line_start()) ("Bad uadd instruction") }
  | UADDS error                                   { raise_at_line (get_line_start()) ("Bad uadds instruction") }
  | UADC error                                    { raise_at_line (get_line_start()) ("Bad uadc instruction") }
  | UADCS error                                   { raise_at_line (get_line_start()) ("Bad uadcs instruction") }
  | USUB error                                    { raise_at_line (get_line_start()) ("Bad usub instruction") }
  | USUBC error                                   { raise_at_line (get_line_start()) ("Bad usubc instruction") }
  | USUBB error                                   { raise_at_line (get_line_start()) ("Bad usubb instruction") }
  | USBC error                                    { raise_at_line (get_line_start()) ("Bad usbc instruction") }
  | USBCS error                                   { raise_at_line (get_line_start()) ("Bad usbcs instruction") }
  | USBB error                                    { raise_at_line (get_line_start()) ("Bad usbb instruction") }
  | USBBS error                                   { raise_at_line (get_line_start()) ("Bad usbbs instruction") }
  | UMUL error                                    { raise_at_line (get_line_start()) ("Bad umul instruction") }
  | UMULL error                                   { raise_at_line (get_line_start()) ("Bad umull instruction") }
  | USPLIT error                                  { raise_at_line (get_line_start()) ("Bad usplit instruction") }
  | USPL error                                    { raise_at_line (get_line_start()) ("Bad uspl instruction") }
  | SADD error                                    { raise_at_line (get_line_start()) ("Bad sadd instruction") }
  | SADDS error                                   { raise_at_line (get_line_start()) ("Bad sadds instruction") }
  | SADC error                                    { raise_at_line (get_line_start()) ("Bad sadc instruction") }
  | SADCS error                                   { raise_at_line (get_line_start()) ("Bad sadcs instruction") }
  | SSUB error                                    { raise_at_line (get_line_start()) ("Bad ssub instruction") }
  | SSUBC error                                   { raise_at_line (get_line_start()) ("Bad ssubc instruction") }
  | SSUBB error                                   { raise_at_line (get_line_start()) ("Bad ssubb instruction") }
  | SSBC error                                    { raise_at_line (get_line_start()) ("Bad ssbc instruction") }
  | SSBCS error                                   { raise_at_line (get_line_start()) ("Bad ssbcs instruction") }
  | SSBB error                                    { raise_at_line (get_line_start()) ("Bad ssbb instruction") }
  | SSBBS error                                   { raise_at_line (get_line_start()) ("Bad ssbbs instruction") }
  | SMUL error                                    { raise_at_line (get_line_start()) ("Bad smul instruction") }
  | SMULL error                                   { raise_at_line (get_line_start()) ("Bad smull instruction") }
  | SSPLIT error                                  { raise_at_line (get_line_start()) ("Bad ssplit instruction") }
  | SSPL error                                    { raise_at_line (get_line_start()) ("Bad sspl instruction") }
  | SHL error                                     { raise_at_line (get_line_start()) ("Bad shl instruction") }
  | SHLS error                                    { raise_at_line (get_line_start()) ("Bad shls instruction") }
  | SHR error                                     { raise_at_line (get_line_start()) ("Bad shr instruction") }
  | SHRS error                                    { raise_at_line (get_line_start()) ("Bad shrs instruction") }
  | SAR error                                     { raise_at_line (get_line_start()) ("Bad sar instruction") }
  | SARS error                                    { raise_at_line (get_line_start()) ("Bad sars instruction") }
  | CSHL error                                    { raise_at_line (get_line_start()) ("Bad cshl instruction") }
  | CSHLS error                                   { raise_at_line (get_line_start()) ("Bad cshls instruction") }
  | CSHR error                                    { raise_at_line (get_line_start()) ("Bad cshr instruction") }
  | CSHRS error                                   { raise_at_line (get_line_start()) ("Bad cshrs instruction") }
  | ROL error                                     { raise_at_line (get_line_start()) ("Bad rol instruction") }
  | ROR error                                     { raise_at_line (get_line_start()) ("Bad ror instruction") }
  | NONDET error                                  { raise_at_line (get_line_start()) ("Bad nondet instruction") }
  | CALL ID LPAR error                            { raise_at_line (get_line_start()) (("Invalid actuals in the call instruction: " ^ $2)) }
  | CALL error                                    { raise_at_line (get_line_start()) ("Bad call instruction") }
  | INLINE ID LPAR error                          { raise_at_line (get_line_start()) (("Invalid actuals in the inline instruction: " ^ $2)) }
  | INLINE error                                  { raise_at_line (get_line_start()) ("Bad inline instruction") }
  | CASE error                                    { raise_at_line (get_line_start()) ("Bad case instruction") }
  | REPEAT error                                  { raise_at_line (get_line_start()) ("Bad repeat instruction") }
;

opt_comma:
    /* empty */                                   { () }
  | COMMA                                         { () }
;

case_values:
    case_value                                    { $1 }
  | case_value COMMA case_values                  { $1 @ $3 }
;

case_value:
    NUM                                           { [$1] }
  | NUM DOTDOT NUM                                { parse_case_range (get_line_start()) $1 $3 }
;

case_body:
    instr                                         { [$1] }
  | instr SEMICOLON                               { [$1] }
  | instr SEMICOLON case_body                     { $1 :: $3 }
;

tagged_bexp_prove_with_list:
    TRUE                                          { fun _ -> (tagged_ebexp_prove_with_singleton Options.Std.default_track [(etrue, [])], tagged_rbexp_prove_with_singleton Options.Std.default_track [(rtrue, [])]) }
  | tagged_ebexp_prove_with_list VBAR tagged_rbexp_prove_with_list
                                                  { fun ctx -> ($1 ctx, $3 ctx) }
;

tagged_ebexp_prove_with_list:
    tagged_ebexp_prove_with                       { fun ctx -> $1 ctx }
  | tagged_ebexp_prove_with DOT tagged_ebexp_prove_with_list
                                                  { fun ctx -> tagged_ebexp_prove_with_union ($1 ctx) ($3 ctx) }
;

tagged_rbexp_prove_with_list:
    tagged_rbexp_prove_with                       { fun ctx -> $1 ctx }
  | tagged_rbexp_prove_with DOT tagged_rbexp_prove_with_list
                                                  { fun ctx -> tagged_rbexp_prove_with_union ($1 ctx) ($3 ctx) }
;

tagged_ebexp_prove_with:
    ebexp_prove_with_list                         { fun ctx -> tagged_ebexp_prove_with_init Options.Std.default_track [($1 ctx)] }
  | ids COLON ebexp_prove_with_list               { fun ctx -> tagged_ebexp_prove_with_inits $1 [($3 ctx)] }
  | MULOP COLON ebexp_prove_with_list             { fun ctx -> tagged_ebexp_prove_with_init Options.Std.all_track [($3 ctx)] }
  | ALL COLON ebexp_prove_with_list               { fun ctx -> tagged_ebexp_prove_with_init Options.Std.all_track [($3 ctx)] }
;

tagged_rbexp_prove_with:
    rbexp_prove_with_list                         { fun ctx -> tagged_rbexp_prove_with_init Options.Std.default_track [($1 ctx)] }
  | ids COLON rbexp_prove_with_list               { fun ctx -> tagged_rbexp_prove_with_inits $1 [($3 ctx)] }
  | MULOP COLON rbexp_prove_with_list             { fun ctx -> tagged_rbexp_prove_with_init Options.Std.all_track [($3 ctx)] }
  | ALL COLON rbexp_prove_with_list               { fun ctx -> tagged_rbexp_prove_with_init Options.Std.all_track [($3 ctx)] }
;

ebexp_prove_with_list:
    ebexp_prove_with                              { fun ctx -> [($1 ctx)] }
  | ebexp_prove_with COMMA ebexp_prove_with_list  { fun ctx -> ($1 ctx)::($3 ctx) }
;

rbexp_prove_with_list:
    rbexp_prove_with                              { fun ctx -> [($1 ctx)] }
  | rbexp_prove_with COMMA rbexp_prove_with_list  { fun ctx -> ($1 ctx)::($3 ctx) }
;

ebexp_prove_with:
    ebexp                                         { fun ctx -> ($1 ctx, []) }
  | ebexp PROVE WITH LSQUARE prove_with_specs RSQUARE
                                                  { fun ctx -> ($1 ctx, $5 ctx) }
  | ebexp PROVE WITH LSQUARE prove_with_specs error
                                                  { raise_at_line (get_line_start()) ("A ] is missing.") }
  | ebexp PROVE WITH LSQUARE error                { raise_at_line (get_line_start()) ("Incorrect prove-with clauses.") }
  | ebexp PROVE WITH error                        { raise_at_line (get_line_start()) ("Enclose the prove-with clauses in [].") }
;

rbexp_prove_with:
    rbexp                                         { fun ctx -> ($1 ctx, []) }
  | rbexp PROVE WITH LSQUARE prove_with_specs RSQUARE
                                                  { fun ctx -> ($1 ctx, $5 ctx) }
  | rbexp PROVE WITH LSQUARE prove_with_specs error
                                                  { raise_at_line (get_line_start()) ("A ] is missing.") }
  | rbexp PROVE WITH LSQUARE error                { raise_at_line (get_line_start()) ("Incorrect prove-with clauses.") }
  | rbexp PROVE WITH error                        { raise_at_line (get_line_start()) ("Enclose the prove-with clauses in [].") }
;

prove_with_specs:
    prove_with_spec                               { fun ctx -> [$1 ctx] }
  | prove_with_spec COMMA prove_with_specs        { fun ctx -> ($1 ctx)::($3 ctx) }
;

prove_with_spec:
    PRECONDITION                                  { fun _ -> Precondition }
  | CUTS LSQUARE const_exp_list RSQUARE           { fun ctx -> Cuts (List.rev_map Z.to_int ($3 ctx) |> List.rev) }
  | ALL CUTS                                      { fun _ -> AllCuts }
  | ALL ASSUMES                                   { fun _ -> AllAssumes }
  | ALL GHOSTS                                    { fun _ -> AllGhosts }
  | ALGEBRA SOLVER ID                             { fun _ -> AlgebraSolver (Options.Std.parse_algebra_solver $3) }
  | ALGEBRA SOLVER SMT COLON path smt_logic_opt   { fun _ -> AlgebraSolver (Options.Std.SMTSolver { algsmt_path = $5; algsmt_logic = $6 }) }
  | RANGE SOLVER path                             { fun _ -> RangeSolver $3 }
  | QFBV SOLVER path                              { fun _ -> RangeSolver $3 }
;

path:
    ID                                            { $1 }
  | PATH                                          { $1 }
;

smt_logic_opt:
                                                  { Options.Std.default_algsmt_option.algsmt_logic }
  | COLON NIA                                     { Options.Std.NIA }
  | COLON LIA                                     { Options.Std.LIA }
  | COLON ID error                                { Stdlib.invalid_arg ("Unknown SMT logic " ^ $2) }
;

ids:
    ID                                            { [ $1 ] }
  | ID COMMA ids                                  { $1::$3 }
;

tagged_bexp:
    TRUE                                          { fun _ -> (tagged_ebexp_singleton Options.Std.default_track etrue, tagged_rbexp_singleton Options.Std.default_track rtrue) }
  | tagged_ebexps VBAR tagged_rbexps              { fun ctx -> ($1 ctx, $3 ctx) }
;

tagged_ebexps:
    tagged_ebexp                                  { fun ctx -> $1 ctx }
  | tagged_ebexp DOT tagged_ebexps                { fun ctx -> tagged_ebexp_union ($1 ctx) ($3 ctx) }
;

tagged_rbexps:
    tagged_rbexp                                  { fun ctx -> $1 ctx }
  | tagged_rbexp DOT tagged_rbexps                { fun ctx -> tagged_rbexp_union ($1 ctx) ($3 ctx) }
;

tagged_ebexp:
    ebexps                                        { fun ctx -> tagged_ebexp_inits [Options.Std.default_track] ($1 ctx) }
  | ids COLON ebexps                              { fun ctx -> tagged_ebexp_inits $1 ($3 ctx) }
  | MULOP COLON ebexps                            { fun ctx -> tagged_ebexp_inits [Options.Std.all_track] ($3 ctx) }
  | ALL COLON ebexps                              { fun ctx -> tagged_ebexp_inits [Options.Std.all_track] ($3 ctx) }
;

tagged_rbexp:
    rbexps                                        { fun ctx -> tagged_rbexp_inits [Options.Std.default_track] ($1 ctx) }
  | ids COLON rbexps                              { fun ctx -> tagged_rbexp_inits $1 ($3 ctx) }
  | MULOP COLON rbexps                            { fun ctx -> tagged_rbexp_inits [Options.Std.all_track] ($3 ctx) }
  | ALL COLON rbexps                              { fun ctx -> tagged_rbexp_inits [Options.Std.all_track] ($3 ctx) }
;

ebexps:
    ebexp COMMA ebexps                            { fun ctx -> ($1 ctx)::($3 ctx) }
  | ebexp                                         { fun ctx -> [$1 ctx] }
  | ebexp error                                   { let lno = get_line_start() in
                                                    fun ctx ->
                                                    raise_at_line lno ("Failed to parse the algebra predicate after '" ^ string_of_ebexp ($1 ctx) ^ "'.")
                                                  }
;

rbexps:
    rbexp                                         { fun ctx -> [$1 ctx] }
  | rbexp COMMA rbexps                            { fun ctx -> ($1 ctx)::($3 ctx) }
  | rbexp COMMA error                             { raise_at_line (get_line_start()) ("Invalid range predicates.") }
  | rbexp error                                   { raise_at_line (get_line_start()) ("A ',' is used to separate range predicates") }
;

ebexp:
    ebexp_primary                                 { fun ctx -> $1 ctx }
  // Scalar
  | EQ eexp_primary eexp_primary                  { parse_ebexp_eq (get_line_start()) $2 $3 }
  | EQMOD eexp_primary eexp_primary eexp_primary  { parse_ebexp_eqmod1 (get_line_start()) $2 $3 $4 }
  | EQMOD eexp_primary eexp_primary LSQUARE eexps RSQUARE
                                                  { parse_ebexp_eqmodN (get_line_start()) $2 $3 $5 }
  | eexp EQOP eexp eq_suffix                      { parse_ebexp_eq_modopt (get_line_start()) $1 $3 $4 }
  | eexp ULTOP eexp                               { parse_ebexp_cmp (get_line_start ()) Elt $1 $3 }
  | eexp ULEOP eexp                               { parse_ebexp_cmp (get_line_start ()) Ele $1 $3 }
  | eexp UGTOP eexp                               { parse_ebexp_cmp (get_line_start ()) Egt $1 $3 }
  | eexp UGEOP eexp                               { parse_ebexp_cmp (get_line_start ()) Ege $1 $3 }
  // Vector
  | EQ veexp_primary veexp_primary                { parse_ebexp_veq (get_line_start()) $2 $3 }
  | EQMOD veexp_primary veexp_primary veexp_primary
                                                  { parse_ebexp_veqmod1 (get_line_start()) $2 $3 $4 }
  | EQMOD veexp_primary veexp_primary LSQUARE veexps RSQUARE
                                                  { parse_ebexp_veqmodN (get_line_start()) $2 $3 $5 }
  | EQMOD veexp_primary veexp_primary LSQUARE veexps RSQUARE ADDADDOP eexp_primary_as_const
                                                  { parse_ebexp_veqmodN_duplicate (get_line_start()) $2 $3 $5 $8 }
  | veexp EQOP veexp veq_suffix                   { parse_ebexp_veq_modopt (get_line_start()) $1 $3 $4 }
  | veexp ULTOP veexp                             { parse_ebexp_vcmp (get_line_start ()) Elt $1 $3 }
  | veexp ULEOP veexp                             { parse_ebexp_vcmp (get_line_start ()) Ele $1 $3 }
  | veexp UGTOP veexp                             { parse_ebexp_vcmp (get_line_start ()) Egt $1 $3 }
  | veexp UGEOP veexp                             { parse_ebexp_vcmp (get_line_start ()) Ege $1 $3 }
  // Logical
  | AND ebexp_primary ebexp_primary               { fun ctx -> Eand ($2 ctx, $3 ctx) }
  | ebexp LANDOP ebexp                            { fun ctx -> Eand ($1 ctx, $3 ctx) }
  | AND LSQUARE ebexps RSQUARE                    { fun ctx -> eands ($3 ctx) }
  | LANDOP LSQUARE ebexps RSQUARE                 { fun ctx -> eands ($3 ctx) }
;

ebexp_primary:
    TRUE                                          { fun _ -> Etrue }
  | LPAR ebexp RPAR                               { fun ctx -> $2 ctx }
;

eq_suffix:
                                                  { fun _ -> None }
  | LPAR MOD eexp RPAR                            { fun ctx -> Some [ $3 ctx ] }
  | LPAR MOD LSQUARE eexps RSQUARE RPAR           { fun ctx -> Some ($4 ctx) }
;

veq_suffix:
                                                  { fun _ -> None }
  | LPAR MOD veexp RPAR                           { fun ctx -> Some (List.rev (List.rev_map (fun e -> [e]) ($3 ctx))) }
  | LPAR MOD LSQUARE veexps RSQUARE RPAR          { fun ctx -> Some ($4 ctx) }
;

cmpop_infix:
    ULTOP                                         { Rult }
  | ULEOP                                         { Rule }
  | UGTOP                                         { Rugt }
  | UGEOP                                         { Ruge }
  | SLTOP                                         { Rslt }
  | SLEOP                                         { Rsle }
  | SGTOP                                         { Rsgt }
  | SGEOP                                         { Rsge }
;

eexp_primary:
    defined_var                                   { parse_eexp_defined_var (get_line_start()) $1 }
  | const                                         { fun ctx -> Econst ($1 ctx) }
  | LPAR eexp RPAR                                { fun ctx -> $2 ctx }
;

eexp_primary_as_const:
  eexp_primary                                    { parse_eexp_as_constant (get_line_start()) $1 }
;

eexp:
    eexp_primary                                  { $1 }
  | veexp_primary LSQUARE NUM RSQUARE             { parse_eexp_vec_elem (get_line_start()) $1 $3 }
  | NEG eexp_primary                              { fun ctx -> eneg ($2 ctx) }
  | ADD eexp_primary eexp_primary                 { fun ctx -> eadd ($2 ctx) ($3 ctx) }
  | SUB eexp_primary eexp_primary                 { fun ctx -> esub ($2 ctx) ($3 ctx) }
  | MUL eexp_primary eexp_primary                 { fun ctx -> emul ($2 ctx) ($3 ctx) }
  | SQ eexp_primary                               { fun ctx -> esq ($2 ctx) }
  | ADDS LSQUARE eexps RSQUARE                    { fun ctx -> eadds ($3 ctx) }
  | MULS LSQUARE eexps RSQUARE                    { fun ctx -> emuls ($3 ctx) }
  | SUBOP eexp %prec UMINUS                       { fun ctx -> eneg ($2 ctx) }
  | eexp ADDOP eexp                               { fun ctx -> eadd ($1 ctx) ($3 ctx) }
  | eexp SUBOP eexp                               { fun ctx -> esub ($1 ctx) ($3 ctx) }
  | eexp MULOP eexp                               { fun ctx -> emul ($1 ctx) ($3 ctx) }
  | eexp POWOP eexp_primary_as_const              { parse_eexp_pow (get_line_start()) $1 $3 }
  | ULIMBS const_exp_primary LSQUARE eexps RSQUARE
                                                  { fun ctx -> limbs (Z.to_int ($2 ctx)) ($4 ctx) }
  | POLY eexp LSQUARE eexps RSQUARE               { fun ctx -> poly ($2 ctx) ($4 ctx) }
;

eexps:
    eexp COMMA eexps                              { fun ctx -> ($1 ctx)::($3 ctx) }
  | eexp                                          { fun ctx -> [$1 ctx] }
  | VARS var_expansion                            { fun ctx -> List.rev (List.rev_map evar ($2 ctx)) }
  | VARS var_expansion COMMA eexps                { fun ctx -> List.rev_append (List.rev_map evar ($2 ctx)) ($4 ctx) }
  | MULOP veexp_primary                           { fun ctx -> $2 ctx }
  | MULOP veexp_primary COMMA eexps               { fun ctx -> List.rev_append (List.rev ($2 ctx)) ($4 ctx) }
;

veexp_primary:
    VEC_ID                                        { let lno = get_line_start() in
                                                    fun ctx ->
                                                    let vec = `AVECT { vecname = $1; vectyphint = None; } in
                                                    let (_, atoms) = (resolve_vec_with ~with_ghost:true ctx lno vec) in
                                                    let es = List.rev_map eexp_of_atom (List.rev_map (resolve_atom_with ctx lno) atoms) in
                                                    es
                                                  }
  | const AT vectyp                               { let lno = get_line_start() in
                                                    fun ctx ->
                                                    let vec = `AVCONST { csttype = $3; cstvalue = $1 } in
                                                    let (_, atoms) = (resolve_vec_with ~with_ghost:true ctx lno vec) in
                                                    let es = List.rev_map eexp_of_atom (List.rev_map (resolve_atom_with ctx lno) atoms) in
                                                    es
                                                  }
  | LSQUARE eexps RSQUARE                         { fun ctx -> $2 ctx }
  | LPAR veexp RPAR                               { fun ctx -> $2 ctx }
;

veexp:
    veexp_primary                                 { $1 }
  | veexp_primary LSQUARE ranges RSQUARE          { parse_veexp_slices (get_line_start()) $1 $3 }
  | NEG veexp_primary                             { parse_veexp_neg (get_line_start()) $2 }
  | ADD veexp_primary veexp_primary               { parse_veexp_add (get_line_start()) $2 $3 }
  | SUB veexp_primary veexp_primary               { parse_veexp_sub (get_line_start()) $2 $3 }
  | MUL veexp_primary veexp_primary               { parse_veexp_mul (get_line_start()) $2 $3 }
  | SQ veexp_primary                              { parse_veexp_sq (get_line_start()) $2 }
  | ADDS LSQUARE veexps RSQUARE                   { parse_veexp_adds (get_line_start()) $3 }
  | MULS LSQUARE veexps RSQUARE                   { parse_veexp_muls (get_line_start()) $3 }
  | SUBOP veexp %prec UMINUS                      { parse_veexp_neg (get_line_start()) $2 }
  | veexp ADDADDOP veexp                          { parse_veexp_append (get_line_start()) $1 $3 }
  | veexp ADDADDOP eexp_primary_as_const          { parse_veexp_duplicate (get_line_start()) $1 $3 }
  | veexp ADDOP veexp                             { parse_veexp_add (get_line_start()) $1 $3 }
  | veexp SUBOP veexp                             { parse_veexp_sub (get_line_start()) $1 $3 }
  | veexp MULOP veexp                             { parse_veexp_mul (get_line_start()) $1 $3 }
  | veexp POWOP eexp_primary_as_const             { parse_veexp_pow (get_line_start()) $1 $3 }
  | veexp POWOP LSQUARE const_exp_list RSQUARE    { parse_veexp_pows (get_line_start()) $1 $4 }
  | ULIMBS const_exp_primary LSQUARE veexps RSQUARE
                                                  { parse_veexp_limbs (get_line_start()) $2 $4 }
  | POLY eexp LSQUARE veexps RSQUARE              { parse_veexp_poly (get_line_start()) $2 $4 }
  | POLY veexp_primary LSQUARE veexps RSQUARE     { parse_veexp_polyv (get_line_start()) $2 $4 }
;

veexps:
    veexp COMMA veexps                            { fun ctx -> ($1 ctx)::($3 ctx) }
  | veexp                                         { fun ctx -> [$1 ctx] }
;

rbexp:
    rbexp_primary                                 { $1 }
  // Scalar
  | EQ rexp_primary rexp_primary                  { parse_rbexp_eq (get_line_start()) $2 $3 }
  | cmpop_prefix rexp_primary rexp_primary        { parse_rbexp_cmp (get_line_start()) $1 $2 $3 }
  | EQMOD rexp_primary rexp_primary rexp_primary  { parse_rbexp_equmod (get_line_start()) $2 $3 $4 }
  | EQUMOD rexp_primary rexp_primary rexp_primary { parse_rbexp_equmod (get_line_start()) $2 $3 $4 }
  | EQSMOD rexp_primary rexp_primary rexp_primary { parse_rbexp_eqsmod (get_line_start()) $2 $3 $4 }
  | EQSREM rexp_primary rexp_primary rexp_primary { parse_rbexp_eqsrem (get_line_start()) $2 $3 $4 }
  | rexp EQOP rexp req_suffix                     { parse_rbexp_eq_modopt (get_line_start()) $1 $3 $4 }
  | rexp cmpop_infix rexp                         { parse_rbexp_cmp (get_line_start()) $2 $1 $3 }
  // Vector
  | EQ vrexp_primary vrexp_primary                { parse_rbexp_veq (get_line_start()) $2 $3 }
  | cmpop_prefix vrexp_primary vrexp_primary      { parse_rbexp_vcmp (get_line_start()) $1 $2 $3 }
  | EQMOD vrexp_primary vrexp_primary vrexp_primary
                                                  { parse_rbexp_vequmod (get_line_start()) $2 $3 $4 }
  | EQUMOD vrexp_primary vrexp_primary vrexp_primary
                                                  { parse_rbexp_vequmod (get_line_start()) $2 $3 $4 }
  | EQSMOD vrexp_primary vrexp_primary vrexp_primary
                                                  { parse_rbexp_veqsmod (get_line_start()) $2 $3 $4 }
  | EQSREM vrexp_primary vrexp_primary vrexp_primary
                                                  { parse_rbexp_veqsrem (get_line_start()) $2 $3 $4 }
  | vrexp EQOP vrexp vreq_suffix                  { parse_rbexp_veq_modopt (get_line_start()) $1 $3 $4 }
  | vrexp cmpop_infix vrexp                       { parse_rbexp_vcmp (get_line_start()) $2 $1 $3 }
  // Logical
  | NEG rbexp_primary                             { fun ctx -> Rneg ($2 ctx) }
  | NEGOP rbexp_primary                           { fun ctx -> Rneg ($2 ctx) }
  | AND rbexp_primary rbexp_primary               { fun ctx -> Rand ($2 ctx, $3 ctx) }
  | OR rbexp_primary rbexp_primary                { fun ctx -> Ror ($2 ctx, $3 ctx) }
  | rbexp LANDOP rbexp                            { fun ctx -> Rand ($1 ctx, $3 ctx) }
  | rbexp LOROP rbexp                             { fun ctx -> Ror ($1 ctx, $3 ctx) }
  | AND LSQUARE rbexps RSQUARE                    { fun ctx -> rands ($3 ctx) }
  | LANDOP LSQUARE rbexps RSQUARE                 { fun ctx -> rands ($3 ctx) }
  | OR LSQUARE rbexps RSQUARE                     { fun ctx -> rors ($3 ctx) }
  | LOROP LSQUARE rbexps RSQUARE                  { fun ctx -> rors ($3 ctx) }
;

rbexp_primary:
    TRUE                                          { fun _ -> Rtrue }
  | LPAR rbexp RPAR                               { fun ctx -> $2 ctx }
;

req_suffix:
                                                  { fun _ -> None }
  | LPAR MOD rexp RPAR                            { fun ctx -> Some (reqmod, $3 ctx) }
  | LPAR UMOD rexp RPAR                           { fun ctx -> Some (reqmod, $3 ctx) }
  | LPAR SMOD rexp RPAR                           { fun ctx -> Some (reqsmod, $3 ctx) }
  | LPAR SREM rexp RPAR                           { fun ctx -> Some (reqsrem, $3 ctx) }
;

vreq_suffix:
                                                  { fun _ -> None }
  | LPAR MOD vrexp RPAR                           { fun ctx -> Some (reqmod, $3 ctx) }
  | LPAR UMOD vrexp RPAR                          { fun ctx -> Some (reqmod, $3 ctx) }
  | LPAR SMOD vrexp RPAR                          { fun ctx -> Some (reqsmod, $3 ctx) }
  | LPAR SREM vrexp RPAR                          { fun ctx -> Some (reqsrem, $3 ctx) }
;

cmpop_prefix:
    ULT                                           { Rult }
  | ULE                                           { Rule }
  | UGT                                           { Rugt }
  | UGE                                           { Ruge }
  | SLT                                           { Rslt }
  | SLE                                           { Rsle }
  | SGT                                           { Rsgt }
  | SGE                                           { Rsge }
;

rexp_primary:
    defined_var                                   { parse_rexp_defined_var (get_line_start()) $1 }
  | CONST const_exp_primary const_exp_primary     { parse_rexp_const (get_line_start()) $2 $3 }
  | CONST typ const_exp_primary                   { parse_rexp_const (get_line_start()) (fun _ -> Z.of_int (size_of_typ $2)) $3 }
  | const_exp_primary AT const_exp_primary        { parse_rexp_const (get_line_start()) $3 $1 }
  | const_exp_primary AT typ                      { parse_rexp_const (get_line_start()) (fun _ -> Z.of_int (size_of_typ $3)) $1 }
  | LPAR rexp RPAR                                { fun ctx -> $2 ctx }
;

rexp:
    rexp_primary                                  { $1 }
  | vrexp_primary LSQUARE NUM RSQUARE             { parse_rexp_vec_elem (get_line_start()) $1 $3 }
  | UEXT rexp_primary const_exp_primary           { parse_rexp_uext (get_line_start()) $2 $3 }
  | SEXT rexp_primary const_exp_primary           { parse_rexp_sext (get_line_start()) $2 $3 }
  | NEG rexp_primary                              { parse_rexp_neg (get_line_start()) $2 }
  | NEGOP rexp_primary                            { parse_rexp_neg (get_line_start()) $2 }
  | NOT rexp_primary                              { parse_rexp_not (get_line_start()) $2 }
  | NOTOP rexp_primary                            { parse_rexp_not (get_line_start()) $2 }
  | ADD rexp_primary rexp_primary                 { parse_rexp_add (get_line_start()) $2 $3 }
  | SUB rexp_primary rexp_primary                 { parse_rexp_sub (get_line_start()) $2 $3 }
  | MUL rexp_primary rexp_primary                 { parse_rexp_mul (get_line_start()) $2 $3 }
  | UDIV rexp_primary rexp_primary                 { parse_rexp_udiv (get_line_start()) $2 $3 }
  | SQ rexp_primary                               { parse_rexp_sq (get_line_start()) $2 }
  | UMOD rexp_primary rexp_primary                { parse_rexp_umod (get_line_start()) $2 $3 }
  | SDIV rexp_primary rexp_primary                { parse_rexp_sdiv (get_line_start()) $2 $3 }
  | SREM rexp_primary rexp_primary                { parse_rexp_srem (get_line_start()) $2 $3 }
  | SMOD rexp_primary rexp_primary                { parse_rexp_smod (get_line_start()) $2 $3 }
  | AND rexp_primary rexp_primary                 { parse_rexp_and (get_line_start()) $2 $3 }
  | OR rexp_primary rexp_primary                  { parse_rexp_or (get_line_start()) $2 $3 }
  | XOR rexp_primary rexp_primary                 { parse_rexp_xor (get_line_start()) $2 $3 }
  | SHL rexp_primary rexp_primary                 { parse_rexp_shl (get_line_start()) $2 $3 }
  | SHR rexp_primary rexp_primary                 { parse_rexp_shr (get_line_start()) $2 $3 }
  | SAR rexp_primary rexp_primary                 { parse_rexp_sar (get_line_start()) $2 $3 }
  | ROL rexp_primary rexp_primary                 { parse_rexp_rol (get_line_start()) $2 $3 }
  | ROR rexp_primary rexp_primary                 { parse_rexp_ror (get_line_start()) $2 $3 }
  | CONCAT rexp_primary rexp_primary              { parse_rexp_concat (get_line_start()) $2 $3 }
  | ADDS LSQUARE rexps RSQUARE                    { parse_rexp_adds (get_line_start()) $3 }
  | MULS LSQUARE rexps RSQUARE                    { parse_rexp_muls (get_line_start()) $3 }
  | ULIMBS const_exp_primary LSQUARE rexps RSQUARE
                                                  { parse_rexp_ulimbs (get_line_start()) $2 $4 }
  | SLIMBS const_exp_primary LSQUARE rexps RSQUARE
                                                  { parse_rexp_slimbs (get_line_start()) $2 $4 }
  // Concatenate all elements (from low to high) in a vector as one bit-vector
  | JOIN vrexp_primary                            { parse_rexp_join_vexpr (get_line_start()) $2 }
  | rexp ADDOP rexp                               { parse_rexp_add (get_line_start()) $1 $3 }
  | rexp SUBOP rexp                               { parse_rexp_sub (get_line_start()) $1 $3 }
  | rexp MULOP rexp                               { parse_rexp_mul (get_line_start()) $1 $3 }
  | rexp ANDOP rexp                               { parse_rexp_and (get_line_start()) $1 $3 }
  | rexp OROP rexp                                { parse_rexp_or (get_line_start()) $1 $3 }
  | rexp XOROP rexp                               { parse_rexp_xor (get_line_start()) $1 $3 }
  | rexp SHLOP rexp                               { parse_rexp_shl (get_line_start()) $1 $3 }
  | rexp SHROP rexp                               { parse_rexp_shr (get_line_start()) $1 $3 }
  | rexp SAROP rexp                               { parse_rexp_sar (get_line_start()) $1 $3 }
  /* Errors */
  | CONST const_exp_primary error                 { raise_at_line (get_line_start()) "Please specify the bit-width of a constant in range predicates" }
  | const_exp_primary error                       { raise_at_line (get_line_start()) "Please specify the bit-width of a constant in range predicates" }
;

vrexp_primary:
    VEC_ID                                        { let lno = get_line_start() in
                                                    fun ctx ->
                                                    let vec = `AVECT { vecname = $1; vectyphint = None; } in
                                                    let (_, atoms) = (resolve_vec_with ~with_ghost:true ctx lno vec) in
                                                    let es = List.rev_map rexp_of_atom (List.rev_map (resolve_atom_with ctx lno) atoms) in
                                                    es
                                                  }
  | LSQUARE rexps RSQUARE                         { fun ctx -> $2 ctx }
  | const_exp_primary AT vectyp                   { let lno = get_line_start() in
                                                    fun ctx ->
                                                    let vec = `AVCONST { csttype = $3; cstvalue = $1 } in
                                                    let (_, atoms) = (resolve_vec_with ~with_ghost:true ctx lno vec) in
                                                    let es = List.rev_map rexp_of_atom (List.rev_map (resolve_atom_with ctx lno) atoms) in
                                                    es
                                                  }
  | LPAR vrexp RPAR                               { fun ctx -> $2 ctx }
;

vrexp:
    vrexp_primary                                 { $1 }
  | vrexp_primary LSQUARE ranges RSQUARE          { parse_vrexp_slices (get_line_start()) $1 $3 }
  | UEXT vrexp_primary const_exp_primary          { parse_vrexp_uext (get_line_start()) $2 $3 }
  | SEXT vrexp_primary const_exp_primary          { parse_vrexp_sext (get_line_start()) $2 $3 }
  | NEG vrexp_primary                             { parse_vrexp_neg (get_line_start()) $2 }
  | NEGOP vrexp_primary                           { parse_vrexp_neg (get_line_start()) $2 }
  | NOT vrexp_primary                             { parse_vrexp_not (get_line_start()) $2 }
  | NOTOP vrexp_primary                           { parse_vrexp_not (get_line_start()) $2 }
  | ADD vrexp_primary vrexp_primary               { parse_vrexp_add (get_line_start()) $2 $3 }
  | SUB vrexp_primary vrexp_primary               { parse_vrexp_sub (get_line_start()) $2 $3 }
  | MUL vrexp_primary vrexp_primary               { parse_vrexp_mul (get_line_start()) $2 $3 }
  | UDIV vrexp_primary vrexp_primary              { parse_vrexp_udiv (get_line_start()) $2 $3 }
  | SQ vrexp_primary                              { parse_vrexp_sq (get_line_start()) $2 }
  | UMOD vrexp_primary vrexp_primary              { parse_vrexp_umod (get_line_start()) $2 $3 }
  | SDIV vrexp_primary vrexp_primary              { parse_vrexp_sdiv (get_line_start()) $2 $3 }
  | SREM vrexp_primary vrexp_primary              { parse_vrexp_srem (get_line_start()) $2 $3 }
  | SMOD vrexp_primary vrexp_primary              { parse_vrexp_smod (get_line_start()) $2 $3 }
  | AND vrexp_primary vrexp_primary               { parse_vrexp_and (get_line_start()) $2 $3 }
  | OR vrexp_primary vrexp_primary                { parse_vrexp_or (get_line_start()) $2 $3 }
  | XOR vrexp_primary vrexp_primary               { parse_vrexp_xor (get_line_start()) $2 $3 }
  | SHL vrexp_primary vrexp_primary               { parse_vrexp_shl (get_line_start()) $2 $3 }
  | SHR vrexp_primary vrexp_primary               { parse_vrexp_shr (get_line_start()) $2 $3 }
  | SAR vrexp_primary vrexp_primary               { parse_vrexp_sar (get_line_start()) $2 $3 }
  | ROL vrexp_primary vrexp_primary               { parse_vrexp_rol (get_line_start()) $2 $3 }
  | ROR vrexp_primary vrexp_primary               { parse_vrexp_ror (get_line_start()) $2 $3 }
  // Element-wise bit-vector concatenation of two vectors
  | CONCAT vrexp_primary vrexp_primary            { parse_vrexp_concat (get_line_start()) $2 $3 }
  | ADDS LSQUARE vrexps RSQUARE                   { parse_vrexp_adds (get_line_start()) $3 }
  | MULS LSQUARE vrexps RSQUARE                   { parse_vrexp_muls (get_line_start()) $3 }
  | ULIMBS const_exp_primary LSQUARE vrexps RSQUARE
                                                  { parse_vrexp_ulimbs (get_line_start()) $2 $4 }
  | SLIMBS const_exp_primary LSQUARE vrexps RSQUARE
                                                  { parse_vrexp_slimbs (get_line_start()) $2 $4 }
  | vrexp ADDADDOP vrexp                          { parse_vrexp_append (get_line_start()) $1 $3 }
  | vrexp ADDOP vrexp                             { parse_vrexp_add (get_line_start()) $1 $3 }
  | vrexp SUBOP vrexp                             { parse_vrexp_sub (get_line_start()) $1 $3 }
  | vrexp MULOP vrexp                             { parse_vrexp_mul (get_line_start()) $1 $3 }
  | vrexp ANDOP vrexp                             { parse_vrexp_and (get_line_start()) $1 $3 }
  | vrexp OROP vrexp                              { parse_vrexp_or (get_line_start()) $1 $3 }
  | vrexp XOROP vrexp                             { parse_vrexp_xor (get_line_start()) $1 $3 }
  | vrexp SHLOP vrexp                             { parse_vrexp_shl (get_line_start()) $1 $3 }
  | vrexp SHROP vrexp                             { parse_vrexp_shr (get_line_start()) $1 $3 }
  | vrexp SAROP vrexp                             { parse_vrexp_sar (get_line_start()) $1 $3 }
;

rexps:
    rexp COMMA rexps                              { parse_rexps_cons (get_line_start()) $1 $3 }
  | rexp                                          { fun ctx -> [$1 ctx] }
  | VARS var_expansion                            { fun ctx -> List.map (fun v -> Rvar v) ($2 ctx) }
;

vrexps:
    vrexp COMMA vrexps                            { parse_vrexps_cons (get_line_start()) $1 $3 }
  | vrexp                                         { fun ctx -> [$1 ctx] }
;

lval:
    ID                                            { `LVPLAIN { lvname = $1; lvtyphint = None; } }
  | ID AT typ                                     { `LVPLAIN { lvname = $1; lvtyphint = Some $3; } }
  | typ ID                                        { `LVPLAIN { lvname = $2; lvtyphint = Some $1; } }
  | ID AT error                                   { raise_at_line (get_line_start()) ("Invalid type of variable " ^ $1) }
;

lval_v:
    VEC_ID                                        { `LVVECT { vecname = $1; vectyphint = None; } }
  | lval_v_nonbare                                { $1 }
;

/* A vector destination that cannot be mistaken for the start of an indexed
   one, because it ends in a type or a bracket of its own */
lval_v_nonbare:
    VEC_ID AT vectyp                              { `LVVECT { vecname = $1; vectyphint = Some $3; } }
  | LSQUARE lval_scalars RSQUARE                  { `LVVLIT $2 }
;

lval_scalars:
    lval                                          { [$1] }
  | lval COMMA lval_scalars                       { $1::$3 }
;

actuals:
    actual_atoms                                  { parse_actuals_all (get_line_start()) $1 }
  | actual_atoms SEMICOLON actual_atoms           { parse_actuals_ins_outs (get_line_start()) $1 $3 }
  |                                               { fun _ _ -> [] }
;

actual_atoms:
    actual_atom                                   { fun ctx tys -> $1 ctx tys }
  | actual_atom COMMA actual_atoms                { fun ctx tys ->
                                                    let (tys, vs1) = $1 ctx tys in
                                                    let (tys, vs2) = $3 ctx tys in
                                                    (tys, List.rev_append (List.rev vs1) vs2)
                                                  }
;

/* We don't check if the actual variables are defined or not because they may just be variable names of procedure outputs. */
actual_atom:
    actual_atom_primary                           { $1 }
  | atom_v                                        { parse_actual_atom_vec (get_line_start()) $1 }
;

actual_atom_primary:
    const_exp                                     { parse_actual_atom (get_line_start()) (`ACONST { atmtyphint = None; atmvalue = $1 }) }
  | const_exp_primary AT typ                      { parse_actual_atom (get_line_start()) (`ACONST { atmtyphint = Some $3; atmvalue = $1 }) }
  | typ const_exp                                 { parse_actual_atom (get_line_start()) (`ACONST { atmtyphint = Some $1; atmvalue = $2 }) }
  | ID                                            { parse_actual_atom (get_line_start()) (`AVAR { atmtyphint = None; atmname = $1 }) }
  | ID OROP NUM DOTDOT NUM                        { parse_actual_atom_var_expansion (get_line_start()) $1 $3 $5 }
/* The following rule produces shift/reduce conflict */
/*  | VEC_ID LSQUARE NUM RSQUARE                    { parse_actual_atom (get_line_start()) (`AVECELM { avecname = $1; avecindex = Z.to_int $3 }) } */
;

atom:
    const_exp_primary                             { `ACONST { atmtyphint = None; atmvalue = $1; } }
  | const_exp_primary AT typ                      { `ACONST { atmtyphint = Some $3; atmvalue = $1; } }
  | typ const_exp_primary                         { `ACONST { atmtyphint = Some $1; atmvalue = $2; } }
  | defined_var                                   { ($1 :> atom_t) }
  | VEC_ID LSQUARE const_exp RSQUARE              { `AVECELM { avecname = $1; avecindex = $3 } }
  /*| LPAR atom RPAR                              { fun ctx -> $2 ctx } source of reduce/reduce conflict*/
;

atom_v:
    atom_v_primary                                { $1 }
  | atom_v_primary LSQUARE ranges RSQUARE         { `AVECSEL { vecselatm = $1; vecselrng = $3 } }
  /* low ++ high */
  | atom_v ADDADDOP atom_v                        { `AVECCAT [$1; $3] }
  | atom_v ADDADDOP const_exp_primary             { `AVECDUP ($1, $3) }
;

/* atom_v without a leading vector literal, so that a bracket following a
   vector destination can only belong to that destination */
atom_v_primary_nolit:
    VEC_ID                                        { `AVECT { vecname = $1; vectyphint = None; } }
  | VEC_ID AT vectyp                              { `AVECT { vecname = $1; vectyphint = Some $3; } }
  | const_exp_primary AT vectyp                   { `AVCONST { csttype = $3; cstvalue = $1 } }
  | LPAR atom_v RPAR                              { $2 }
;

atom_v_nolit:
    atom_v_primary_nolit                          { $1 }
  | atom_v_primary_nolit LSQUARE ranges RSQUARE   { `AVECSEL { vecselatm = $1; vecselrng = $3 } }
  | atom_v_nolit ADDADDOP atom_v                  { `AVECCAT [$1; $3] }
  | atom_v_nolit ADDADDOP const_exp_primary       { `AVECDUP ($1, $3) }
;

atom_v_primary:
    VEC_ID                                        { `AVECT { vecname = $1; vectyphint = None; } }
  | VEC_ID AT vectyp                              { `AVECT { vecname = $1; vectyphint = Some $3; } }
  | LSQUARE atom_scalars RSQUARE                  { `AVLIT $2 }
  | const_exp_primary AT vectyp                   { `AVCONST { csttype = $3; cstvalue = $1 } }
  | LPAR atom_v RPAR                              { $2 }
;

atom_scalars:
    atom                                          { [$1] }
  | atom COMMA atom_scalars                       { $1::$3 }
;

ranges:
    ranges_slicing                                { $1 }
  | ranges_indices                                { $1 }
;

ranges_slicing:
    range_slicing                                 { [$1] }
  | range_slicing COMMA ranges_slicing            { $1::$3 }
;

ranges_indices:
  const_exp COMMA const_exp_list                  { [ SelSingle (fun ctx -> Z.to_int ($1 ctx)); SelMultiple (fun ctx -> (List.rev_map Z.to_int ($3 ctx) |> List.rev)) ] }
;

range_slicing:
    const_exp COLON const_exp                     { SelRange (fun ctx -> (Some (Z.to_int ($1 ctx)), Some (Z.to_int ($3 ctx)), None)) }
  |               COLON const_exp                 { SelRange (fun ctx -> (None, Some (Z.to_int ($2 ctx)), None)) }
  | const_exp COLON                               { SelRange (fun ctx -> (Some (Z.to_int ($1 ctx)), None, None)) }
  | const_exp COLON const_exp COLON const_exp
                                                  { SelRange (fun ctx -> (Some (Z.to_int ($1 ctx)), Some (Z.to_int ($3 ctx)), Some (Z.to_int ($5 ctx)))) }
  |               COLON const_exp COLON const_exp
                                                  { SelRange (fun ctx -> (None, Some (Z.to_int ($2 ctx)), Some (Z.to_int ($4 ctx)))) }
  | const_exp COLON               COLON const_exp
                                                  { SelRange (fun ctx -> (Some (Z.to_int ($1 ctx)), None, Some (Z.to_int ($4 ctx)))) }
;

var_expansion:
  ID OROP NUM DOTDOT NUM                          { parse_var_expansion (get_line_start()) $1 $3 $5 }
;

defined_var:
    ID                                            { parse_defined_var (get_line_start()) $1 None }
  | ID AT typ                                     { parse_defined_var (get_line_start()) $1 (Some $3) }
  | typ ID                                        { parse_defined_var (get_line_start()) $2 (Some $1) }
;

gvars:
    gvar                                          { fun ctx -> ([$1 ctx], []) }
  | vgvar                                         { fun ctx -> ([], [$1 ctx]) }
  | gvar COMMA gvars                              { fun ctx -> let (sgvars, vgvars) = $3 ctx in
                                                               ($1 ctx::sgvars, vgvars) }
  | vgvar COMMA gvars                             { fun ctx -> let (sgvars, vgvars) = $3 ctx in
                                                               (sgvars, $1 ctx::vgvars) }
  | gvar error                                    { raise_at_line (get_line_start()) ("A comma is used to separate ghost variables.") }
  | error                                         { raise_at_line (get_line_start()) ("Invalid ghost variable.") }
;

gvar:
    typ ID                                        { parse_gvar (get_line_start()) $2 $1 }
  | ID AT typ                                     { parse_gvar (get_line_start()) $1 $3 }
;

vgvar:
    vectyp VEC_ID                                 { parse_vgvar (get_line_start()) $2 $1 }
  | VEC_ID AT vectyp                              { parse_vgvar (get_line_start()) $1 $3 }
;

const_exp_list:
    const_exp                                     { fun ctx -> [$1 ctx] }
  | const_exp COMMA const_exp_list                { fun ctx -> ($1 ctx)::($3 ctx) }
;

const_exp:
    const_exp_primary                             { fun ctx -> $1 ctx }
  | SUBOP const_exp %prec UMINUS                  { fun ctx -> Z.neg ($2 ctx) }
  | const_exp ADDOP const_exp                     { fun ctx -> Z.add ($1 ctx) ($3 ctx) }
  | const_exp SUBOP const_exp                     { fun ctx -> Z.sub ($1 ctx) ($3 ctx) }
  | const_exp MULOP const_exp                     { fun ctx -> Z.mul ($1 ctx) ($3 ctx) }
  | const_exp POWOP const_exp                     { fun ctx ->
                                                    let n = $1 ctx in
                                                    let i = $3 ctx in
                                                    try
                                                      Z.pow n (Z.to_int i)
                                                    with Z.Overflow ->
                                                      big_pow n i
                                                  }
;

const_exp_primary:
    const                                         { fun ctx -> $1 ctx }
  | LPAR const_exp RPAR                           { fun ctx -> $2 ctx }
;

const_exp_primarys:
    const_exp_primary                             { [$1] }
  | const_exp_primary COMMA const_exp_primarys    { $1::$3 }
;

const_exp_v_primary:
  LSQUARE const_exp_primarys RSQUARE              { $2 }

;

const:
    NUM                                           { fun _ -> $1 }
  | DEREFOP ID                                    { parse_named_constant (get_line_start()) $2 }
;

typ:
    UINT                                          { if $1 > 0 then uint_t $1
                                                    else raise_at_line (get_line_start()) ("The big-width must be positive") }
  | SINT                                          { if $1 > 0 then int_t $1
                                                    else raise_at_line (get_line_start()) ("The big-width must be positive") }
  | BIT                                           { bit_t }
;

vectyp:
  typ LSQUARE NUM RSQUARE                         { let dim = Z.to_int $3 in
                                                    if dim > 0 then ($1, dim)
                                                    else raise_at_line (get_line_start()) ("Vector length must be positive") }

nums:
    NUM                                           { [Z.to_int $1] }
  | NUM COMMA nums                                { Z.to_int $1::$3 }
;

atom_vs:
    atom_v_primary                                { [$1] }
  | atom_v_primary atom_vs                        { $1::$2 }
;
