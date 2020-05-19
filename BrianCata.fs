// Réf https://lorgonblog.wordpress.com/2008/05/

type 'a Tree = 
    | Node of data:'a * left:'a Tree * right:'a Tree 
    | Leaf

let FoldTree fNode fLeaf tree : 'r =  
    let rec recurse t cont =  
        match t with  
        | Node(x, left, right) ->
            recurse left  (fun lacc ->   
            recurse right (fun racc ->  
            cont (fNode x lacc racc)))  
        | Leaf -> cont fLeaf  
    recurse tree id

let Change9to0 tree =
    FoldTree (fun x l r -> Node((if x=9 then 0 else x), l, r)) Leaf tree

// XFold
let XFoldTree fNode fLeaf tree : 'r =  
    let rec recurse t cont =  
        match t with  
        | Node(x, left, right) ->
            recurse left  (fun lacc ->   
            recurse right (fun racc ->  
            cont (fNode x lacc racc t)))  
        | Leaf -> cont (fLeaf t)
    recurse tree id

let (===) = fun x y -> obj.ReferenceEquals(x, y)

let Xnode (x, l, r) (Node(xo, lo, ro) as orig) =
    if (xo = x) && (lo === l) && (ro === r) then
        orig
    else
        Node(x, l, r)

let XLeaf (Leaf as orig) =
    Leaf

let XChange5to0 tree =
    XFoldTree (fun x l r -> Xnode((if x=5 then 0 else x), l, r)) XLeaf tree

// KFold
// Warning : Not tail recursive : 
// "recurse left" computed then fed to "k" in "(fun k -> k (recurse left))""
let KFoldTree fNode fLeaf tree : 'r =
    let rec recurse t =
        match t with
        | Leaf -> fLeaf t
        | Node(x, left, right) ->
            fNode x (fun k -> k (recurse left)) (fun k -> k (recurse right)) t 
    recurse tree

let Change5to0bst tree =
    let fNode x kl kr t =
        let (Node(_, oldl, oldr)) = t
        if x < 5 then
            kr (fun newr -> Node (x, oldl, newr))
        elif x > 5 then
            kl (fun newl -> Node (x, newl, oldr))
        else
            Node (0, oldl, oldr)
    KFoldTree fNode id tree

// Helper to prove KFoldTree causes a stack overflow : creates tree with size "size"
let CreateZeroRightTree size =
    let rec recurse n t =
        if n < size then
            let newt = Node(0, Leaf, t)
            recurse (n+1) newt
        else
            t
    recurse 0 Leaf

// Tail recursive supposedly : but stills does bring a stack overflow according to my tests
let KFoldTree2 fNode fLeaf tree : 'r =
    let rec recurse t k =
        match t with
        | Leaf -> fLeaf t k
        | Node(x, left, right) ->
            fNode x (recurse left) (recurse right) t k
    recurse tree id

let Change5to0bst2 tree =
    let fNode x kl kr t k =
        let (Node(_, leftold, rightold)) = t
        if x < 5 then
            kr (fun newright -> k (Node(x, leftold, newright)))
        elif x > 5 then
            kl (fun newleft -> k (Node(x, newleft, rightold)))
        else
            k (Node(0, leftold, rightold))
    let fLeaf t k = k t
    KFoldTree2 fNode fLeaf tree

// Back to the mini-language using KFold
type Op = 
    | Plus 
    | Minus 
type Expr = 
    | Literal of int 
    | BinaryOp of Expr * Op * Expr
    | IfThenElse of Expr * Expr * Expr // cond, then, else; 0=false in cond
    | Print of Expr 

// Warning : Not tail recursive : 
// "recurse left" computed then fed to "k" in "(fun k -> k (recurse left))""
let KFoldExpr fLit fBin fIf fPrint expr : 'r =
    let rec recurse ex =
        match ex with
        | Literal(n) -> fLit n ex
        | BinaryOp(left, op, right) ->
            fBin op (fun k -> k (recurse left)) (fun k -> k (recurse right)) ex
            // in fBin, "k" variable is the continuation down the tree to and including the current node level
            // "recurse left" and "recurse right" are for the lower parts
        | IfThenElse (i, t, e) ->
            fIf (fun k -> k (recurse i)) (fun k -> k (recurse t)) (fun k -> k (recurse e)) ex
            // k : same meaning as above
        | Print(e) ->
            fPrint (fun k -> k (recurse e)) ex
    recurse expr

let Eval expr =
    let fLit n _ = n
    let fBin op kl kr _ =
        match op with
        | Plus -> kl (fun lval -> kr (fun rval -> lval + rval))
        | Minus -> kl (fun lval -> kr (fun rval -> lval - rval))
    let fIf kcond kthen kelse ex =
        kcond (fun cval ->
            match cval with
            | 0 -> kelse id
            | _ -> kthen id
        )
    let fPrint k _ =
        k (fun kval ->
            printfn "<%i>" kval
            kval
        )
    KFoldExpr fLit fBin fIf fPrint expr

// Tests
let tree7 =
    Node(4, Node(2, Node(1, Leaf, Leaf), Node(3, Leaf, Leaf)),
        Node(6, Node(5, Leaf, Leaf), Node(7, Leaf, Leaf)))

printfn "\n---------- Test XFoldTree :"
printfn "With XFold : %A" (XChange5to0 tree7)

printfn "\n---------- Test KFoldTree (not tail recursive) :"
printfn "With KFold : %A" (Change5to0bst tree7)

printfn "\n---------- Test stack overflow with KFoldTree :"
let bigtree = CreateZeroRightTree 2000000
// printfn "Bigtree With KFold : %A" (Change5to0bst bigtree)

printfn "\n---------- Test stack overflow with KFoldTree2 :"
printfn "Bigtree With KFold : %A" (Change5to0bst2 bigtree)

// Tests mini-language
let exprs = [Literal(42)
             BinaryOp(Literal(1), Plus, Literal(1)) 
             IfThenElse(Literal(1), Print(Literal(42)), Print(Literal(0))) 
            ]

exprs |> List.iter (Eval >> printfn "%d") 