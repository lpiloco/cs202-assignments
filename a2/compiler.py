from typing import List, Set, Dict, Tuple
import sys
import traceback

from cs202_support.python import *
import cs202_support.x86 as x86

# Input Language: LVar
# op ::= "add"
# Expr ::= Var(x) | Constant(n) | Prim(op, [Expr])
# Stmt ::= Assign(x, Expr) | Print(Expr)
# LVar ::= Program([Stmt])

gensym_num = 0

def gensym(x):
    """
    Constructs a new variable name guaranteed to be unique.
    :param x: A "base" variable name (e.g. "x")
    :return: A unique variable name (e.g. "x_1")
    """

    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'


##################################################
# remove-complex-opera*
##################################################

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lvar program
    :return: An Lvar program with atomic operator arguments.
    """

    #- rco_exp compiles an expression
    #This should always return an atomic expression
    def rco_exp(e: Expr, bindings: Dict[str, Expr]) -> Expr:
        match e:
        #- Constant or Var expression: just return it(already atomic)
            case Constant(n):
                return Constant(n)
            case Var(x):
                return Var(x)
        #- Prim expression:
            case Prim(op, args):
                # Recursive call to rco_exp should make the argument atomic
                new_args =[]
                for a in args:
                    new_args.append(rco_exp(a, bindings))
                # new_args =[rco_exp(a, bindings) for a in args]   This does the same thing
                tmp = gensym('tmp')
                # Bind tmp to Prim(op, new_args)
                bindings[tmp] = Prim(op, new_args)
                return Var(tmp)


            #- For each argument to the Prim, create a new temporary variable(if needed) and bind it to the result of compiling the argument expression
            #- We can store new bindings in the environment: str -> Expr
    #- rco_stmt compiles a statement
    def rco_stmt(s: Stmt) -> Stmt:
        #rco_stmt compiles a statement
        #- Assign(x, e): call rco_exp on e
        #- Print(e): call rco_exp on e
        #- Challenge: what about bindings?
        pass
    #- rco_stmts compiles a list of statements
    def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:
        #- rco_stmts compiles a list of statements
        new_stmts = []
        #- For each stmt
        for stmt in stmts:
            bindings = {}
        #- call rco_stmt on the stmt
            new_stmt = rco_stmt(stmt, bindings)
        #TODO: turn each binding statement into assignment statement
        # x --> e ===> Assign(x, e)
        #TODO: Add each binding assignment to new_stmts
        new_stmts.append(new_stmt)
        pass

    return Program(rco_stmts(prog.stmts))


##################################################
# select-instructions
##################################################

# Output language: pseudo-x86
# ATM ::= Immediate(n) | Var(x) | Reg(str)
# instr_name ::= "movq" | "addq"
# Instr ::= NamedInstr(instr_name, [Atm]) | Callq(str) | Retq()
# X86 ::= X86Program(Dict[str, [Instr]])

def select_instructions(prog: Program) -> x86.X86Program:
    """
    Transforms a Lvar program into a pseudo-x86 assembly program.
    :param prog: a Lvar program
    :return: a pseudo-x86 program
    """

    #- si_atm converts an LVar atomic into an x86 atomic
    def si_atm(atm: Expr) -> x86.Arg:
        pass
    #- si_stmt converts an LVar statement into one or more x86 instruction
    def si_stmt(stmt: Stmt) -> List[x86.Instr]:
        match stmt:
            case Assign(x, Prim('add', [atm1, atm2])):
                pass
            case Assign(x, atm1):
                pass
            case print(atm1):
                pass
    #- si_stmts compiles a list of statements
    def si_stmts(stmts: List[Stmt]) -> List[x86.Instr]:
        instrs = []

        for stmt in stmts:
            i = si_stmt(stmt)
            instrs.extend(i)

        return instrs

    pass


##################################################
# assign-homes
##################################################

def assign_homes(program: x86.X86Program) -> x86.X86Program:
    """
    Assigns homes to variables in the input program. Allocates a stack location for each
    variable in the program.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the amount of stack space used
    """

    pass


##################################################
# patch-instructions
##################################################

def patch_instructions(program: x86.X86Program) -> x86.X86Program:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    pass


##################################################
# prelude-and-conclusion
##################################################

def prelude_and_conclusion(program: x86.X86Program) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """

    pass


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'remove complex opera*': rco,
    'select instructions': select_instructions,
    'assign homes': assign_homes,
    'patch instructions': patch_instructions,
    'prelude & conclusion': prelude_and_conclusion,
    'print x86': x86.print_x86
}


def run_compiler(s, logging=False):
    def print_prog(current_program):
        print('Concrete syntax:')
        if isinstance(current_program, x86.X86Program):
            print(x86.print_x86(current_program))
        elif isinstance(current_program, Program):
            print(print_program(current_program))

        print()
        print('Abstract syntax:')
        print(print_ast(current_program))

    current_program = parse(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print_prog(current_program)

    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print_prog(current_program)

    return current_program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                x86_program = run_compiler(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except:
                print('Error during compilation! **************************************************')
                traceback.print_exception(*sys.exc_info())
