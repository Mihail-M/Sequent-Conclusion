open SequentHelper
open SequentHelper.Declarations
open SequentHelper.SequentProverHelper
open SequentHelper.SequentPrintHelper

let seq1 = [var "A" => (var "A" * var "B")] --> []
let seq2 = [var "p" * var "q"] --> [!(! (var "p") * !(var "q"))]
let seq3 = [!(var "A") => !(var "B")] --> [!((var "A" ||| var "B" * var "A") => var "B")] 

let test = seq2
if check test then printfn "This sequent is Derivable!\n"
else printfn "This sequent is not Derivable!\n"

printfn "This is conclution "

printProofTree (applying test)









