  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $48, %rsp
  movq $1, %rax
  addq $2, %rax
  movq %rax, -8(%rbp)
  movq -8(%rbp), %rax
  addq $3, %rax
  movq %rax, -16(%rbp)
  movq -16(%rbp), %rax
  movq %rax, -24(%rbp)
  movq $5, -32(%rbp)
  movq -24(%rbp), %rax
  addq -32(%rbp), %rax
  movq %rax, -40(%rbp)
  movq -40(%rbp), %rdi
  callq print_int
  addq $48, %rsp
  popq %rbp
  retq
