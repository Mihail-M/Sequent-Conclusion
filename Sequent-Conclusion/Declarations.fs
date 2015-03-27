namespace SequentHelper 
    module Declarations =

        type Var = V of string
        type Connective = And | Or | Implication | Not
        type Formula = FVar of Var| Op of Connective*Formula*Formula
        //sintax sugar 
        let var x = FVar (V x)
        let (|||) a b = Op(Or,a,b)
        let (*) a b = Op(And, a, b)
        let (!) b = Op(Not, b, var "")
        let (=>) a b = Op(Implication, a, b)

        type Sequent = Sequent of Formula list * Formula list 
        let (-->) a b = Sequent(a,b)

        type Side = Antecedent | Succedent

        type Label = Derivable | NotDerivable | Unknown

        type Tree<'a, 'b> =  Leaf of 'b 
                            | Bend of 'a * Tree<'a, 'b> // возникает в случае однопосылочного вызова
                            | Branch of 'a * Tree<'a, 'b> * Tree<'a,'b> // двухпосылочный


        type ProofTree = Tree of (Sequent*string)*(Sequent*Label) 
        //для инициализации 
        let SeqWithLabel x y = (Sequent (x, y), Unknown)

        //пересечение 2-х списков. Из стандартного нашел только какой-то изврат с set
        let rec intersect a b =
            match a with
            |h::t -> match b with
                        |h2::t2 -> 
                            if h = h2 then h::(intersect t t2)
                            else if h > h2 then intersect t b else intersect a t2
                        |[] -> []
            |[] -> []

        let rec (>>=) x f = 
                match x with 
                    | Leaf (b) -> f b 
                    | Bend (a, b) -> Bend(a, b >>= f)
                    | Branch(a, b, c) -> Branch(a, b >>= f, c >>= f)
        
        let rec FoldTree f g h x = 
            match x with
            |Leaf(a) -> f a
            |Bend(a, b) -> g a (FoldTree f g h b)
            |Branch(a, b, c)-> h a (FoldTree f g h b) (FoldTree f g h c)

        let isVar x =
            match x with
            |FVar(_) -> true
            |_ -> false