namespace SequentHelper
open SequentHelper.Declarations

    module SequentProverHelper =
        //опишем правила вывода 
        let rule formula side seq = 
            match formula, side, seq with
                    |Op (Not, q, _), Antecedent, Sequent(a, b) -> 
                            Bend( (Sequent(formula::a, b), "! ->"), Leaf(SeqWithLabel a (q::b) ) )
                    |Op (Not, q, _), Succedent, Sequent(a, b) ->
                                Bend( (Sequent(a, formula::b),"-> !"), Leaf(SeqWithLabel (q::a) b ) )
                    |Op (And, q, w), Antecedent, Sequent (a, b) ->
                                Bend( (Sequent (formula::a, b), "/\\ ->"), (Leaf (SeqWithLabel (q::w::a) b)) )
                    |Op (And, q, w), Succedent, Sequent (a, b) -> 
                            Branch( (Sequent (a, formula::b), "-> /\\"), Leaf (SeqWithLabel a (q::b) ), Leaf (SeqWithLabel a (w::b) ) )
                    |Op (Or, q, w), Succedent, Sequent (a, b) -> 
                            Bend((Sequent (a, formula::b), "-> \/"), Leaf(SeqWithLabel (q::w::a) b) )
                    |Op (Or, q, w), Antecedent, Sequent (a, b) ->
                                Branch((Sequent (formula::a, b), "\/ ->"), Leaf(SeqWithLabel (q::a) b ), Leaf(SeqWithLabel (w::a) b) )
                    |Op (Implication, q, w), Antecedent, Sequent (a, b) -> 
                            Branch((Sequent (formula::a, b), "=> ->"), Leaf(SeqWithLabel a (q::b) ), Leaf(SeqWithLabel (w::a) b))
                    |Op (Implication, q, w), Succedent, Sequent (a, b) -> 
                            Bend((Sequent (formula::a, b), "-> => "), Leaf(SeqWithLabel (q::a) (w::b) ) )
                    |FVar(_), _, Sequent(a, b) -> //сюда мы на самом деле не придем, 
                                                    //так как будем давать на вход этой функции 
                                                    //только норм правила. Это просто заглушка, позже уберем ее
                            Leaf(SeqWithLabel a b ) 

        (*Для того, чтобы не давать на вход функции rule просто переменные, определим функцию, которая будет 
            превравращать антецедент и сукседент в 4 списка: просто переменных и логических связок антицедента и сукцедента соответственно
            Назовем это нормальной секвенциальной формой ( вроде бы это определение не занято))
        *)

        type NormalSequentForm =  NormalSequentForm of Var List * Formula List * Var List * Formula List
        let toVar x =  match x with
                            |FVar(a) -> a 
                            |Op(_, a, _) -> V("-1") // заглушка

        

        let split f  = List.fold (fun (y, z) x -> if f x then (x::y, z) else (y, x::z)) ([],[]) 
        let splitVar = split isVar

        let toNormalSequentForm seq = 
            match seq with
                |Sequent (a,b) ->
                    let normalAntecedent = splitVar a
                    let normalSuccedent = splitVar b
                    NormalSequentForm (List.map toVar (fst normalAntecedent), snd normalAntecedent, 
                        List.map toVar (fst normalSuccedent), snd normalSuccedent)


        (*несмотря на то, что нам очень удобно хранить секвекцию в нормальной форме, на вход функции, которая применяет правила и строит проверяющее дерево мы подаем
        секвенцию в обычной форме, поэтому нужно обратное преобразование
        *)
        let toSequent (NormalSequentForm(a,b,c,d)) = Sequent((List.map (fun x-> FVar x) a)@b, (List.map (fun x -> FVar x) c)@d)


        (*
            теперь можно и подумать, как применять наши правила, 
            Главная идея: 
            очевидно, что если мы доведем до "аксиомы" - это когда в сукцеденте и антицеденте содержатся только переменные 
            и хотя бы одна переменная совпадает, то эта аксиома выводима 
        *)
        let applyRule seq = 
            let normSeq = toNormalSequentForm  (fst seq)

            let applyRuleWithNormal (NormalSequentForm(a, b, c, d)) = 
                    if (intersect a c <> [] ) then Leaf(fst seq, Derivable)
                    else if b <> [] then rule b.Head Antecedent (NormalSequentForm (a, b.Tail, c, d) |> toSequent)
                    else if d <> [] then rule d.Head Succedent  (NormalSequentForm (a, b, c, d.Tail) |> toSequent)
                    else Leaf(fst seq, NotDerivable)

            applyRuleWithNormal normSeq

        (*применение правил начинается с исходного секвента, а затем применяется к каждому Leaf, выведенному из исходного*)
        //будем применять правила к секвенциям с метками
        

        let rec unfold f x = 
            match (f x) with
            | Leaf a -> Leaf a
            | b ->  b >>= (unfold f)  
   
        let applying (Sequent(A,B)) = SeqWithLabel A B |> (unfold applyRule) 

        
        let foldProofTree x = FoldTree (fun x->x) (fun x y -> y) (fun x y z -> 
                                                                    match y with  
                                                                    |(a, NotDerivable) -> (a, NotDerivable)
                                                                    |_-> match z with
                                                                            |(b, NotDerivable) -> (b, NotDerivable)
                                                                            |c -> c
                                                                ) x

        let check seq = 
            match (foldProofTree (applying seq)) with 
            |(_, Derivable) -> true
            |_ -> false

  