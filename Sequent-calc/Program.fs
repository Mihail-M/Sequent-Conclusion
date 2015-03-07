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
//для инициализации 
let SeqWithLabel x y = (Sequent (x, y), Unknown)

//опишем правила вывода 
let rule formula side seq = 
    match formula, side, seq with
            |Op (Not, q, _), Antecedent, Sequent(a, b) -> Bend( Sequent(formula::a, b), Leaf(SeqWithLabel a (q::b) )  )
            |Op (Not, q, _), Succedent, Sequent(a, b) -> Bend( Sequent(a, formula::b), Leaf(SeqWithLabel (q::a) b ) )
            |Op (And, q, w), Antecedent, Sequent (a, b) -> Bend( Sequent (formula::a, b), (Leaf (SeqWithLabel (q::w::a) b)) )
            |Op (And, q, w), Succedent, Sequent (a, b) -> Branch( Sequent (a, formula::b), Leaf (SeqWithLabel a (q::b) ), Leaf (SeqWithLabel a (w::b) ) )
            |Op (Or, q, w), Succedent, Sequent (a, b) -> Bend(Sequent (a, formula::b), Leaf(SeqWithLabel (q::w::a) b) )
            |Op (Or, q, w), Antecedent, Sequent (a, b) -> Branch(Sequent (formula::a, b), Leaf(SeqWithLabel (q::a) b ), Leaf(SeqWithLabel (w::a) b) )
            |Op (Implication, q, w), Antecedent, Sequent (a, b) -> Branch(Sequent (formula::a, b), Leaf(SeqWithLabel a (q::b) ), Leaf(SeqWithLabel (w::a) b))
            |Op (Implication, q, w), Succedent, Sequent (a, b) -> Bend(Sequent (formula::a, b), Leaf(SeqWithLabel (q::a) (w::b) ) )
            |Var, _, Sequent(a, b) -> Leaf(SeqWithLabel a b ) //сюда мы на самом деле не придем, так как будем давать на вход этой функции только норм правила. Это просто заглушка, позже уберем ее

