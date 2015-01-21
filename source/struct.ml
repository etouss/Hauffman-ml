open Array;;
open Bitio;;

type 'a tree =
| Feuille of 'a
| Node of int * 'a tree * 'a tree;;

type noeud = {
  mutable key_val : (int*int) tree;
  mutable pere : int;
  mutable fils : int;
  mutable frere_droit : int;
  mutable frere_gauche : int;
  (*mutable marque : bool;*)
  mutable degree : int;
}
;;

type heap ={
  mutable min : int;
  mutable tas : noeud array;
  (*mutable n : int;*)
  roots : (int,int)Hashtbl.t;
  degArr : int array;
}



(*  TAS FIBO   *)

(** Fonction qui prend en argument deux arbre et precise quel arbre est le plus petit par rapport a la fréquence
sert a trier le tas. *)
let plusPetit a b = match a,b with
  |(Feuille(_,a2),Feuille(_,b2))->if a2<=b2 then true else false
  |(Feuille(_,a2),Node(b1,_,_))-> if a2<=b1 then true else false
  |(Node(a1,_,_),Node(b1,_,_))-> if a1<=b1 then true else false
  |(Node(a1,_,_),Feuille(_,b2))->if a1<=b2 then true else false;;

(**Fonction redusant le tableau des char en enlevant tout les Char qui n'appareisent pas dans le/les fichier
elle en profite egalement pour vérifier si un charactere est libre pour l'interoperabilité*)
let reduc (tab:(int*int) array) nb =
  let rec taille (tab:(int*int) array)  i acc n first =
    if i = n then acc,first
    else match tab.(i) with
      | (a,0)->if first != 256 then taille tab (i+1) acc n first
               else (tab.(i)<-(a,nb); taille tab (i+1) (acc+1) n i)
      | _->taille tab (i+1) (acc+1) n first
  in let rec crea ntab tab2 i ni n =
    if i = n then ntab
    else match tab.(i) with
      | (_,0)->crea ntab tab (i+1) ni n
      | (x,y)->ntab.(ni)<-({key_val = Feuille(x,y); pere = -1; fils = -1; frere_droit = ni; frere_gauche = ni; degree=0} );crea ntab tab (i+1) (ni+1) n
  in let t,first = taille tab 0 0 257 (if nb>0 then 256 else 0) in let tab = crea (Array.make t ({key_val = Feuille(0,0); pere = -1; fils = -1; frere_droit = -1; frere_gauche = -1;degree=0} )) tab 0 0 257 in
  {min = -1;tas = tab;roots =Hashtbl.create t;degArr=Array.make (int_of_float (log (float_of_int t)/. log (1.61803398875))+1 ) (-1)},first;;


(** Fonction inserant un noeud dans le tas, et créant les connexion. *)
let inserting_node heap indexNoeud =
  if heap.min = -1 || plusPetit (heap.tas.(indexNoeud).key_val) (heap.tas.(heap.min).key_val)
  then heap.min <- indexNoeud; Hashtbl.add heap.roots indexNoeud indexNoeud;;
(*Concatene list heap ? *)

(** Fonction qui remet a zero les connexion fraternelle d'un noeud*)
let clean heap indexNoeud =
  let n = heap.tas.(indexNoeud) in
  n.pere<-(-1);
  n.frere_droit<-indexNoeud;
  n.frere_gauche<-indexNoeud;;

(** Fonction a inserting_node sauf qu'elle remet a 0 les connexion *)
let inserting_node2 heap indexNoeud key_val=
  let n = heap.tas.(indexNoeud) in
    n.key_val<-key_val;
    n.pere<-(-1);
    n.fils<-(-1);
    n.frere_droit<-indexNoeud;
    n.frere_gauche<-indexNoeud;
    n.degree<-0;
    Hashtbl.add heap.roots indexNoeud indexNoeud;
    if heap.min = -1 || plusPetit (n.key_val) (heap.tas.(heap.min).key_val)
    then heap.min <- indexNoeud;;

(** Fonction ajoutant un noeud a la root du tas *)
let addFilsToRoots heap noeud =
  let rec aux fils init =
    fils.pere <- (-1);
    if fils.frere_droit != init then let _ = Hashtbl.add heap.roots fils.frere_droit fils.frere_droit in
      let r = aux heap.tas.(fils.frere_droit) init in let _ = clean heap noeud.fils in r
    else ()
    in if noeud.fils != -1 then let _ = Hashtbl.add heap.roots noeud.fils noeud.fils in let r = aux heap.tas.(noeud.fils) (noeud.fils) in let _ = clean heap noeud.fils in r
      else ();;


(** Fonction qui creer les connexion entre deux noeud de même degree *)
let link x y heap =
  (*print_string "x:"; print_int x; print_string "y :"; print_int y;*)
  (*heap.roots<-removeFromRoots heap.roots y;*)
  Hashtbl.remove heap.roots y;
  heap.tas.(y).pere <- x;
  if heap.tas.(x).fils != -1 then
    (heap.tas.(y).frere_droit <-  heap.tas.(heap.tas.(x).fils).frere_droit;
    heap.tas.(heap.tas.(x).fils).frere_droit <- y;
    heap.tas.(y).frere_gauche <- heap.tas.(x).fils;
    heap.tas.(x).degree <- heap.tas.(x).degree +1)
  else (heap.tas.(x).fils <- y;
    heap.tas.(x).degree <- heap.tas.(x).degree +1);;


(** Fonction qui vide degArray pour le prochain consolidate et en profite pour mettre a joue le min *)
let raz heap =
  let func x =
    if x = -1 then (-1)
    else if heap.min = (-1) then (heap.min <- x; (-1))
    else if plusPetit (heap.tas.(x).key_val) (heap.tas.(heap.min).key_val)
      then (heap.min <- x; (-1))
    else (-1)
  in let rec aux heap i n =
    if i = n then ()
    else (heap.degArr.(i) <- func heap.degArr.(i) ;aux heap (i+1) n)
  in aux heap 0 (length heap.degArr);;

(** Fonction principal du tas de Fibo. Sont objectif et de mettre ensemble tout les sommet de root de même degrée.
Pour cela elle utilise degArray ou elle stocke l'indice des noeud de même degrée *)
let consolidate heap =
  (*Array.map (fun x -> (-1)) degArray;*)
  let rec parcoursArray  x deg =
  (*print_string "x:"; print_int x; print_string "deg :"; print_int deg;*)
    let y = heap.degArr.(deg) in
      if y = -1 then (x,deg)
      else if plusPetit (heap.tas.(x).key_val) (heap.tas.(y).key_val)
      then ((link x y heap; heap.degArr.(deg)<-(-1); parcoursArray  x (deg+1)))
      else ((link y x heap; heap.degArr.(deg)<-(-1); parcoursArray  y (deg+1)))
    in let func i j =
    let x,deg = parcoursArray i (heap.tas.(i).degree)
    in heap.degArr.(deg)<-x
  in Hashtbl.iter func heap.roots;raz heap;;

(** Fonction recupere le minimum du tas et retire ces connexion *)
let extract_min heap =
  let minIndice = heap.min in
  (*let mini = heap.tas.(heap.min) in*)
    if heap.min != -1 then
  ((*heap.roots <- removeFromRoots heap.roots heap.min;*)
      Hashtbl.remove heap.roots heap.min;
      addFilsToRoots heap heap.tas.(heap.min);
      heap.min <- (-1);let _ = consolidate heap in ();minIndice)
    else
      minIndice;;

(** Fonction qui init le tas en inserant chacun de ces neouds *)
let initHeap heap =
  let rec aux heap i =
    if i = length (heap.tas) then ()
    else (inserting_node heap (i);aux heap (i+1);)
in aux heap 0;;

let creerTasFibo tab nb =
  let heap,first = reduc tab nb in
  let _ = initHeap heap in heap,first;;

let recupKey_val heap indice =
  if indice = -1 then heap.tas.(heap.min).key_val
  else heap.tas.(indice).key_val;;

let length_tas heap =
  length heap.tas;;



(*    TAS STANDARD  *)

(*On se permet de laisser le code des Tas standart car même si moins optimaux que ceux de fibo
leurs implémentation est bien plus fonctionnelle que celle de ceux de Fibo, qui utliser beaucoup de trait impératif*)


(** Fonction qui renvoi l'arbre dont la frequence est la plus petite *)
let min a b = match a,b with
  |(Feuille(_,a2),Feuille(_,b2))->if a2<=b2 then a else b
  |(Feuille(_,a2),Node(b1,_,_))-> if a2<=b1 then a else b
  |(Node(a1,_,_),Node(b1,_,_))-> if a1<=b1 then a else b
  |(Node(a1,_,_),Feuille(_,b2))->if a1<=b2 then a else b;;


(**Fonction redusant le tableau des char en enlevant tout les Char qui n'appareisent pas dans le/les fichier*)
let reducTas tab nb =
  let rec taille tab i acc n first =
    if i = n then acc,first
    else match tab.(i) with
      | (a,0)->if first != 256 then taille tab (i+1) acc n first
               else (tab.(i)<-(a,nb); taille tab (i+1) (acc+1) n i)
      | _->taille tab (i+1) (acc+1) n first
  in let rec crea ntab tab2 i ni n =
    if i = n then ntab
    else match tab.(i) with
      | (_,0)->crea ntab tab (i+1) ni n
      | (x,y)->ntab.(ni)<-(Feuille(x,y));crea ntab tab (i+1) (ni+1) n
  in let t,first = taille tab 0 0 257 (if nb>0 then 256 else 0)
  in crea (Array.make t (Feuille(0,0))) tab 0 0 257,first;;


(**Fonction entasser Min des tas*)
let entasserMinTas tab i n=
  let getMin a b c tab n =
    if b<n && c<n then
      let res = min (tab.(a)) (min (tab.(b)) (tab.(c))) in
        if res = tab.(a) then a
        else if res = tab.(b) then b
        else c
    else if b<n then
      let res = min (tab.(a)) (tab.(b)) in
        if res = tab.(a) then a
        else b
    else
        a
  and switch a b tab = let temp = tab.(a) in tab.(a)<-(tab.(b));tab.(b)<-temp
  in let rec entAux tab i n =
      let min = getMin i (2*i+1) (2*i+2) tab n in
      if min = i then tab
      else (switch min i tab; entAux tab min n)
in entAux tab i n;;

(**Fonction extraction Min des tas*)
let extractionMinTas tab n =
  let min = tab.(0) in
if n = 1 then min
else
  let _ = tab.(0)<-(tab.(n-1))
  and  _ = entasserMinTas tab 0 (n-1)
  in min;;


(**Fonction extraction Min des tas sans réinjecter le dernier element au début pour laisser une place a la somme*)
let extractionMinTas2 tab n =
  let min = tab.(0) in
if n = 1 then min
else
  let _ = tab.(0)<-(tab.(n-1))
  in min;;

(**Fonction de creation des tas*)
let creerTas tab nb =
    let tabAux,first = reducTas tab nb in
    let rec creerAux tab i =
        if i > -1 then creerAux (entasserMinTas tab i (length tab)) (i-1)
        else tab,first
in creerAux tabAux ((length tab)/2);;
