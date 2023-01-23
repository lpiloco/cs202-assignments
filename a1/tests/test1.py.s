  .globl main
main:
  movq $24, %rdi
  callq print_int
  retq
