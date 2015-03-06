type Var = Var of string
type Connective = And | Or | Implication | Not
type Formula = Var | Op of Connective*Formula*Formula
type Sequent = Sequent of Formula list * Formula list 
type Side = Antecedent | Succedent

type Label = Derivable | NotDerivable | Unknown
type Tree<'a, 'b> =  Leaf of 'b 
                    | Bend of 'a * Tree<'a, 'b> // возникает в случае однопосылочного вызова
                    | Branch of 'a * Tree<'a, 'b> * Tree<'a,'b> // двухпосылочный

type ProofTree = Tree of Sequent*(Sequent*Label) 


