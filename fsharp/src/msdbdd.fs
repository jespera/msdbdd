namespace Msd

module Atom =
  open System

  type elmt = exn ref

  exception Empty

  type Val<'a> (vs : 'a list) =
    inherit Exception("err")
    member __.vs = vs

  let mk() : elmt = ref Empty

  let equal (a : elmt) (b : elmt) = a = b

  let disc (args : (elmt * 'a) list) : 'a list list =
    let folder atoms args =
      match args with
      | atom, v when !atom = Empty ->
        atom := (Val [v] :> exn)
        atom :: atoms
      | atom, v ->
        match !atom with
        | :? Val<_> as va -> atom := (Val <| v :: va.vs) :> exn
        atoms
    let mapper atom =
      match atom with
      | atom when !atom = Empty -> failwith "empty?"
      | atom ->
        match !atom with
        | :? Val<_> as va ->
          atom := Empty
          va.vs
    match args with
    | [] -> []
    | [(_, v)] -> [[v]]
    | args ->
      List.fold folder [] args
        |> List.map mapper

module SimpleDURef =
  type 'a durefC =
    | ECR of 'a * Atom.elmt
    | PTR of 'a duref
  and 'a duref = 'a durefC ref

  let duref x : _ duref = ref <| ECR(x, Atom.mk())

  let rec find (p : _ duref) =
    match !p with
    | ECR _ -> p
    | PTR p' ->
      let p'' = find p'
      p := PTR p''
      p''

  let deref (p : _ duref) =
    match !(find p) with
    | ECR(x,_) -> x
    | PTR _ -> failwith "!!PTR"

  let disc ns =
    ns |> List.map (fun (p, v) ->
      match !(find p) with
      | ECR (_, a) -> a, v
      | PTR _ -> failwith "disc PTR?"
    ) |> Atom.disc

  let equal p p' = (find p) = (find p')
  let update p x =
    let p' = find p
    match !p' with
    | ECR (_, a) ->
      p' := ECR(x,a)
    | PTR _ -> failwith "unexpected PTR in update"

  let link p q =
    let p' = find p
    let q' = find q
    if p' = q'  then () else p' := PTR q'

  let union = link

  let unify f p q =
    let v = f(deref p, deref q)
    union p q
    update q v

module Node =
  open SimpleDURef
  type nodeVal =
    | TRUE
    | FALSE
    | IF of int * nodeVal duref * nodeVal duref
    | APPLY of nodeVal duref * nodeVal duref
  type node = nodeVal duref

  let deref = deref

  let tt = duref TRUE
  let ff = duref FALSE
  let newIf = IF >> duref
  let newApply = APPLY >> duref

  let discNode x = disc x
  let equal x = equal x

  let rec discNodeVal' (trues, falses, ifs, applies) ns =
    match ns with
    | (TRUE, v) :: rest ->
      discNodeVal' (v :: trues, falses, ifs, applies) rest
    | (FALSE, v) :: rest ->
      discNodeVal' (trues, v :: falses, ifs, applies) rest
    | (IF(_,n1,n2), v) :: rest ->
      discNodeVal' (trues, falses, (n1, (n2, v)) :: ifs, applies) rest
    | (APPLY(n1,n2), v) :: rest ->
      discNodeVal' (trues, falses, ifs, (n1, (n2, v)) :: applies) rest
    | [] ->
      let ifDisc = List.map discNode <| discNode ifs
                    |> List.concat
      let appliesDisc = List.map discNode (discNode applies) |> List.concat
      [trues; falses] @ ifDisc @ appliesDisc
        |> List.filter (not << List.isEmpty)

  let discNodeVal args =
    discNodeVal' ([], [], [], []) args
  
  let partitionByContent ns = 
    ns |> List.map (fun n -> deref n, n) |> discNodeVal

  let unify (ns : node list) =
    match ns with
    | [] -> ()
    | n :: ns' -> List.iter (fun n' -> link n' n; ()) ns'
    
module NodeHeap =
  type node = Node.node
  let mk n =
    let m = Array.create n []
    let lookup i = m.[i]
    let update i elmts = m.[i] <- elmts
    let add i elmt = m.[i] <- elmt :: m.[i]
    let app f =
      Array.iteri (fun i elmts -> m.[i] <- f elmts) m
    let revapp f =
      for i = Array.length m - 1 downto 0 do m.[i] <- f m.[i]
    lookup, update, add, app, revapp


