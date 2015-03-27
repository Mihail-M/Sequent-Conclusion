namespace SequentHelper
open SequentHelper.Declarations
open System
    module SequentPrintHelper =
        
        let printLabel = function 
          | Derivable -> "+" 
          | NotDerivable -> "-"
          | Unknown -> "?"



        let rec printFormula A = 
            match A with
                |FVar(V(a)) -> a
                |Op(a, b, c) -> match a with 
                                | Not -> 
                                    if isVar(b) then "!" + printFormula b
                                    else "!(" + printFormula b + ")"
                                | And -> printFormula b + " /\ " + printFormula c
                                | Or -> printFormula b + " \/ " + printFormula c
                                | Implication -> printFormula b  + " => " + printFormula c



        let rec printSequent (Sequent(a,b)) = 
            let rec printListFormula l acc =
                match  l with 
                |[] -> acc
                |h::t -> printListFormula t acc + printFormula h

            printListFormula a "" + " -> " + printListFormula b ""
        
        let printSequentWithLabel (a,b) =
           printSequent a + " " + printLabel b
        let printSequentandRule a = 
            printSequent (fst a) + "    with rule " + (snd a)

        let  printProofTree a =
            let rec printPiece A  = 
                match A with 
                | Bend(a, b) ->     printfn "%A" (printSequentandRule a)
                                    printPiece b 
                | Branch(a, b, c) -> printfn "%A" (printSequentandRule a)
                                     printPiece b  
                                     printPiece c 
                | Leaf(b) -> printfn "%A" (printSequentWithLabel b)
            
            printPiece a
    
