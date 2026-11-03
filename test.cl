proc test() = {
    true && true
}
    mov testVar 0x0@uint64;
{
    true && true
}

proc main() = {
    true && true
}
    mov testVar 0x1@uint64;
    call test();
{
    testVar = 1 && testVar = 1@uint64
}