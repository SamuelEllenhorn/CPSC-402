# README

## Introduction

Copy this directory `Typechecker` into the **private** github repo you are using for your assignments.

To compile run `stack build` and to test run `stack test`.

You should see (among other output)

    Good programs: passed 2 of 76 tests

The above produced a lot of output, sometimes it is useful to just test on one file: To run typechecking on a specific test file, run `stack exec CPPTypeChecker-exe <file_path>.cc`.

The files produced by bnfc are in src:

	AbsCpp.hs
	ErrM.hs
	LexCpp.hs
	ParCpp.hs
	PrintCpp.hs

The template for the typechecker is in `TypeChecker.hs`. This where you will find the code that you need to complete.

To know which cases you need to add, look at the grammar as well as at the algebraic data type for abstract syntax trees defined in `AbsCpp.hs`.

The error monad that is used to modify the type `Type` of CPP-types is defined in `ErrM.hs`.

### Haskell Tips

You can postpone checking out this section until the point where you get stuck in the assignment. I collected some tips in my [Notes on the Typechecker](https://hackmd.io/@alexhkurz/SypNV6qvL).

To look up the type of built-in functions, search the functions at hoogle, see for example [foldM at hoogle](https://hoogle.haskell.org/?hoogle=foldM). Don't forget to click on the little plus sign for a description of how `foldM` works.

#### Further Sources/Helpful links for Haskell

(Collected by Austin Bohannon and Sam Kagan for this assignment.)

##### Base language
* https://wiki.haskell.org/
 * https://wiki.haskell.org/Fold
 * https://wiki.haskell.org/Keywords
 * https://wiki.haskell.org/Monad
 * https://wiki.haskell.org/Anonymous_function
* https://stackoverflow.com/questions/2468332/string-formatting-in-haskell
* https://wiki.haskell.org/How_to_work_on_lists
* https://stackoverflow.com/questions/7564103/haskell-iterate-over-a-list
* https://zvon.org/other/haskell/Outputprelude/zip_f.html

##### Packages
* https://hoogle.haskell.org
* https://hackage.haskell.org/
 * https://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Monad.html
 * https://hackage.haskell.org/package/base-4.12.0.0/docs/Text-Printf.html
 * https://hackage.haskell.org/package/base-4.12.0.0/docs/Prelude.html#v:map
 * https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Tuple.html
* https://stackoverflow.com/questions/5844347/accessing-a-specific-element-in-a-tuple
* https://en.wikibooks.org/wiki/Haskell/Lists_and_tuples

## Assignment 2

## Assignment Typechecker 

(deadlines tba)

The assignment is detailed below but see also the [original source](http://www.grammaticalframework.org/ipl-book/assignments/assignment2/assignment2.html).

### Details

- **First Deadline:**
    - Run `stack build` and `stack test`.
    - The provided template `src/TypeChecker.hs` already passes two good programs in `test/good/`. Which programs are this? 
void_return_empty.cc
good01.cc

    - Find the functions `checkStm` and `inferTypeExp` in `TypeChecker.hs`. Which typechecking rules are already implemented? Hint:
      - Find and open the file `AbsCPP.hs`. Find the data types `Stm` and `Exp`. These are the data types of our abstract syntax tree. 
      - Each line in the definition of `Stm` or `Exp` corresponds to a line in the grammar [cpp.cf](https://github.com/alexhkurz/compiler-construction-2020/blob/master/Sources/Cpp/cpp.cf). Open the grammar in an editor and compare it line by line with `AbsCPP.hs`.
      - The typechecker works by induction (recursion) over the data types `Stm` and `Exp`. For each line in the data type there must be a corresponding case  in `checkStm` or `inferTypeExp`.
    - Find and open the program `easy_add.cc`. 
      - What is the abstract syntax tree of `easy_add.cc`? Hint: 
        - Use [bnfc](https://github.com/alexhkurz/compiler-construction-2020/blob/master/bnfc-tutorial-short.md) to create a parser from the grammar [cpp.cf](https://github.com/alexhkurz/compiler-construction-2020/blob/master/Sources/Cpp/cpp.cf).
         - Then use the parser to create the linearized abstract syntax tree of `easy_add.cc`.
      - Which rule needs to be implemented to typecheck the program `easy_add.cc`? Hint: `PDefs`, `Dfun` and number of other cases are already implemented in `TypeChecker.hs`.
      - Add the corresponding code to the `inferTypeExp` function of `TypeChecker.hs`. Hint: This may look complicated at first sight, but notice that the typechecking for multiplication is already implemented in the template. 
      - After adding the typechecking rule for addition, you should get upon running `stack build` and `stack test`

            Good programs: passed 3 of 76 tests
            Bad programs:  passed 74 of 74 tests
            
    - Which two rules need to be implemented to typecheck the program `ass_easy.cc`?
      - Hint: If you run `stack exec CPPTypeChecker-exe ass_easy.cc` you will get a hint of what the missing rule is. 
      - Hint: To implement the rule, note that you can return a value without writing `return`. In fact, `return` is only needed if you want to typecast a value of type `Env` into a value of type `Err Env`. For now, you can more or less ignore the difference between `Env` and `Err Env`: While `Env` is the type of environments, a value of type `Err Env` is either an environment or an error message. 
    - After building and testing you should now get:
      
            Good programs: passed 5 of 76 tests
            Bad programs:  passed 73 of 74 tests

    - Remark: At the beginning you should focus on increasing the number of passed good programs. And it is probably easier to do first the expressions and then the statements.

    - Before you go on have a quick look at the Haskell tips in my [Notes on the Typechecker](https://hackmd.io/@alexhkurz/SypNV6qvL). 


- **Second Deadline:** Implement the remaining cases until you pass all test programs. As shown above it may be good to pick a short and easy good test program and think about what is needed to make the typechecker pass it. Work through the test programs one by one. It can also be a good idea to create your own test programs.






