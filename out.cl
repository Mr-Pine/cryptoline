proc main (Lcfa_0x008, Lcfa_0x028) =
{
  true
  &&
  true
}

(* main: *)
main:;
(* #! -> SP = 0x7fffffffd388 *)
#! 0x7fffffffd388 = 0x7fffffffd388;
(* sub    $0x8,%rsp *)
sub    $0x8,%rsp;
(* movq   $0x0,(%rsp)                              #! EA = Lcfa_0x008 *)
movq   $0x0,%%Lcfa_0x008                              #! Lcfa_0x008 = Lcfa_0x008;
(* vpbroadcastq (%rsp),%ymm0                       #! EA = L0x008; Value = 0x0000000000000000 0x00007ffff7c2a1ca 0x00007fffffffd3d0 0x00007fffffffd4a8 *)
broadcast %ymm0@sint64[4] 4 [L0x008];
(* movq   $0x42,(%rsp)                             #! EA = Lcfa_0x008 *)
movq   $0x42,%%Lcfa_0x008                             #! Lcfa_0x008 = Lcfa_0x008;
(* movddup (%rsp),%xmm0                            #! EA = Lcfa_0x008; Value = 0x0000000000000042 0x00007ffff7c2a1ca *)
mov %xmm0@uint64[2] [ Lcfa_0x008, Lcfa_0x008 ];
(* sub    $0x20,%rsp *)
sub    $0x20,%rsp;
(* vmovdqa %ymm0,(%rsp)                            #! EA = Lcfa_0x028 *)
mov [Lcfa_0x028,Lcfa_0x020,Lcfa_0x018,Lcfa_0x010] %ymm0@uint64[4];
(* mov    (%rsp),%rax                              #! EA = Lcfa_0x028; Value = 0x0000000000000042 *)
mov rax Lcfa_0x028;
(* add    $0x28,%rsp *)
add    $0x28,%rsp;
(* #! <- SP = 0x7fffffffd388 *)
#! 0x7fffffffd388 = 0x7fffffffd388;
(* #ret *)
#ret;

{
  true
  &&
  true
}

