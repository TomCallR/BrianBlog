// Ref : https://lorgonblog.wordpress.com/2008/04/05/catamorphisms-part-one/

type 'a Tree =
    | Leaf
    | Node of data:'a * left:'a Tree * right:'a Tree

module List =

    let rec Fold combine acc alist : 'r =
        match alist with
        | [] -> acc
        | h::t -> Fold combine (combine h acc) t

    let FoldBack combine alist acc =
        let rec recurse blist cont =
            match blist with
            | [] -> cont acc
            | h::t ->
                let newcont = fun racc -> cont (combine h racc)
                recurse t newcont
        recurse alist id

module Tree =

    let SumTree tree =
        let rec recurse tree acc =
            match tree with
            | Leaf -> acc
            | Node (data, left, right) ->
                (acc + data) |> recurse left |> recurse right
        recurse tree 0
    
    let rec InOrder tree =
        match tree with
        | Leaf -> []
        | Node (data, left, right) ->
            (InOrder left) @ [data] @ (InOrder right)

    let Height tree =
        let rec recurse tree acc =
            match tree with
            | Leaf -> acc
            | Node (_, left, right) ->
                max (recurse left (acc + 1)) (recurse right (acc + 1))
        recurse tree 0

    let Fold fNode acc tree : 'r =
        let rec recurse tree cont =
            match tree with
            | Leaf -> cont acc
            | Node (data, left, right) ->
                let innercont x lacc racc = cont (fNode x lacc racc)
                recurse left (fun lacc -> recurse right (fun racc -> innercont data lacc racc))
        recurse tree id

    let Fold2 fNode acc tree : 'r =
        let rec recurse tree cont =
            match tree with
            | Leaf -> cont acc
            | Node (data, left, right) ->
                let innercont x lacc racc = cont (fNode x lacc racc)
                let lacc = recurse left cont
                let racc = recurse right cont
                innercont data lacc racc
        recurse tree id

// module Language =
// types capable of representing a small integer expression language
type Op =
    | Plus
    | Minus 
    override this.ToString() =
        match this with
        | Plus -> "+"
        | Minus -> "-"
type Expr =
    | Literal of int
    | BinaryOp of Expr * Op * Expr
    | IfThenElse of Expr * Expr * Expr
    | Print of Expr

module Language =

    let FoldExpr fLit fBin fIf fPrint e : 'r =
        let rec recurse e cont =
            match e with 
            | Literal(n) -> cont (fLit n)
            | BinaryOp(left, op, right) ->
                let newcont racc op lacc = cont (fBin racc op lacc)
                recurse left (fun lacc -> recurse right (fun racc ->
                    newcont racc op lacc))
            | IfThenElse(cond, truecase, falsecase) ->
                let newcont cacc tacc facc = cont (fIf cacc tacc facc)
                recurse cond (fun cacc -> recurse truecase (fun tacc ->
                    recurse falsecase (fun facc -> newcont cacc tacc facc)))
            | Print(elem) -> recurse elem (fPrint >> cont)
        recurse e id

    let PrettyPrint e =
        let fLit n = sprintf "%i" n
        let fBin left op right = sprintf "%s %s %s" left (op.ToString()) right
        let fIf cacc tacc facc = sprintf "if %s then %s else %s endif" cacc tacc facc
        let fPrint elem = sprintf "print(%s)" elem
        FoldExpr fLit fBin fIf fPrint e

    let NaiveEval e =
        let fLit n = n
        let fBin left op right = 
            match op with
            | Plus -> left + right
            | Minus -> left - right
        let fIf cacc tacc facc =
            match cacc with
            | 0 -> facc
            | _ -> tacc
        let fPrint elem =
            printfn "<%d>" elem
            elem
        FoldExpr fLit fBin fIf fPrint e

    let Eval e =
        let fLit n () = n
        let fBin left op right () = 
            match op with
            | Plus -> left () + right ()
            | Minus -> left () - right ()
        let fIf cacc tacc facc () =
            match cacc () with
            | 0 -> facc ()
            | _ -> tacc ()
        let fPrint elem () =
            printfn "<%d>" (elem ())
            elem ()
        FoldExpr fLit fBin fIf fPrint e ()

// Tests
printfn "Fold : Somme %A" (List.Fold (+) 0 [1..5])
printfn "Fold : Liste inversée %A" (List.Fold (fun e acc -> e::acc) [] [1..5])
// printfn "FoldBack : Liste %A" 
(List.FoldBack (fun e _ -> printf "%i " e) [1..5] ())
printfn ""

let tree7 = Node(4, Node(2, Node(1, Leaf, Leaf), Node(3, Leaf, Leaf)),
                    Node(6, Node(5, Leaf, Leaf), Node(7, Leaf, Leaf)))
printfn " * Fonctions spécifiques :"
printfn "Somme Tree : %i" (Tree.SumTree tree7)
printfn "InOrder Tree : %A" (Tree.InOrder tree7)
printfn "Height Tree : %i" (Tree.Height tree7)
printfn " * Idem avec Fold :"
printfn "Somme Tree : %i" (Tree.Fold (fun x lacc racc -> x + lacc + racc) 0 tree7)
printfn "Somme Tree (not tail rec) : %i" (Tree.Fold2 (fun x lacc racc -> x + lacc + racc) 0 tree7)
printfn "InOrder Tree : %A" (Tree.Fold (fun x lacc racc -> lacc @ [x] @ racc) [] tree7)
printfn "InOrder Tree (not tail rec) : %A" (Tree.Fold2 (fun x lacc racc -> lacc @ [x] @ racc) [] tree7)
printfn "Height Tree : %i" (Tree.Fold (fun x lacc racc -> 1 + (max lacc racc)) 0 tree7)
printfn "Height Tree (not tail rec) : %i" (Tree.Fold2 (fun x lacc racc -> 1 + (max lacc racc)) 0 tree7)
printfn " * InOrder amélioré :"
printfn "InOrder Tree : %A" ((Tree.Fold (fun x lacc racc acc -> lacc (x::(racc acc))) id tree7) [])

let exprs = [Literal(42)
             BinaryOp(Literal(1), Plus, Literal(1))
             IfThenElse(Literal(1), Print(Literal(42)), Print(Literal(0)))
            ]
printfn "----- Mini Language -----"
printfn " * PrettyPrint "
exprs |> List.map (Language.PrettyPrint >> (printfn "%s")) |> ignore
printfn " * NaiveEval "
exprs |> List.map (Language.NaiveEval >> (printfn "%d")) |> ignore
printfn " * Eval "
exprs |> List.map (Language.Eval >> (printfn "%d")) |> ignore