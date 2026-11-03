.intel_syntax noprefix
.global main

main:
    sub rsp, 8
    mov QWORD PTR [rsp], 0
    vpbroadcastq ymm0, [rsp]
    mov QWORD PTR [rsp], 0x42
    movddup xmm0, [rsp]
    sub rsp, 32
    vmovdqa [rsp], ymm0
    mov rax, [rsp]
    add rsp, 40
    ret