open Struct;;
open Unix;;
open Bitio;;
open Array;;

exception SystemFileFailComp of string;;

(*      ENCODAGE    *)

(** Créer un tableau contenant l'ensemble des char possible et le EOF
(tuple pour stocker les frequences et le char) *)
let init () = let f i (x,y) = (i,y) in Array.mapi f (Array.make 257 (0,0));;

(** Fonction qui prend en argument deux arbre et renvoie la somme de la frequence de deux arbre *)
let somme a b = match a,b with
  |(Feuille(_,a2),Feuille(_,b2))->(a2+b2)
  |(Feuille(_,a2),Node(b1,_,_))->(a2+b1)
  |(Node(a1,_,_),Node(b1,_,_))->(a1+b1)
  |(Node(a1,_,_),Feuille(_,b2))->(a1+b2);;

(** Fonction prenant en argument le chemin d'un fichier et renvoyant un tuple(relativePath,Name)  *)
let splitDirName file =
  let rec aux i j n file =
    if i = n then j
    else
      match String.get file i with
      |'/'-> aux (i+1) (i+1) n file
      |_-> aux (i+1) j n file
  in let j = aux 0 0 (String.length file) file
in ((String.sub file 0 j),(String.sub file j ((String.length file) - j)));;

(** Fonction simulant la representation d'un arbre pour renvoyer la taille prise en bits *)
let simuleRepresentation_arbre a =
  let rec aux a taille = match a with
    |Feuille(l,_) -> if l < 255 then taille+9
                     else if l = 255 then taille+10
                     else taille+10
    |Node(_,g,d) -> let nTaille = taille+1 in let nnTaille = aux g nTaille in aux d nnTaille
in aux a 0;;

(** Fonction parcourant l'ensemble d'un fichier pour mettre a jour la frequence des charactere d'un tableau *)
(*On profite de se parcours pour calculer un nombre MD5 permettant de savoir si la décompression c'est bien passer*)
let freqFile file tab arbo dir booleanDir=
  let input = open_in_bit (dir^file) in
  let nArbo = List.rev (file::(List.rev arbo)) in
  let rec aux input tab md5=
    match input_bit_byte input with
      | 256 -> if booleanDir then nArbo,md5
               else let a,_ = tab.(256) in let _=  tab.(256)<-(a,1) in nArbo,md5
      | x -> let a,b = tab.(x) in tab.(x)<-(a,(b+1)); aux input tab (md5+x)
  in let a,md5 = aux input tab 0
in close_in_bit input;(a,(String.length file + 1),(md5 mod 1073741824));;

(** Fonction equivalente a freq file mais realisant l'operation sur un repertoire complet *)
(* On profite de ce parcours pour creer un tableau representant l'arborescence*)
let rec freqDir fifo tab arbo taille real md5 nb=
  if Queue.is_empty fifo then (arbo,taille,md5,nb)
  else
    let dir = Queue.pop fifo in
    let nTaille = taille + String.length dir + 1 in
    let nArbo = List.rev (dir::(List.rev arbo)) in
    let files = Sys.readdir (real^dir) in
    (*if length files = 0 then freqDir fifo tab nArbo nTaille real md5
    else*)
    let rec parcours files i n arbo taille md5 nb=
          if i = n then (arbo,taille,md5,nb)
          else let name = files.(i) in
            if Sys.is_directory (real^dir^name) then (Queue.add (dir^name^"/") fifo; parcours files (i+1) n arbo) taille md5 (nb+1)
            else let a,t,md = freqFile name tab arbo (real^dir) true in  parcours files (i+1) n a (t+taille) ((md5+md) mod 1073741824) (nb+1)
    in let a,t,md5,nnb = parcours files 0 (length files) nArbo nTaille md5 0
    in let b = freqDir fifo tab a t real md5 (nnb+nb) in let _ = tab.(256)<-(256,1) in b;;


(**Fonction de algorythme d'hauffman creer un arbre a partir d'un tas*)
let hauffManTas tab =
  let add tab x n =  let _ = tab.(0)<-x in entasserMinTas tab 0 n in
  let rec aux tab n =
    if n < 2 then tab
    else
       let min1 = extractionMinTas tab n
       in let min2 = extractionMinTas2 tab (n-1)
       in let node = Node((somme min1 min2),min1,min2)
       in let _ =  add tab node (n-1)
       in aux tab (n-1)
  in (aux tab (length tab)).(0);;

(**Fonction de algorythme d'hauffman creer un arbre a partir d'un tas de fibo*)
let hauffMan heap =
(*let add tab x n =  let _ = tab.(0)<-x in entasserMin tab 0 n in*)
let rec aux heap n =
  if n < 2
    then recupKey_val heap (-1)
  else
    let min1 = extract_min heap
    in let min2 = extract_min heap
    in let node = Node(somme (recupKey_val heap min1) (recupKey_val heap min2),recupKey_val heap min1,recupKey_val heap min2)
    in let _ =  inserting_node2 heap min2 node in
    aux heap (n-1)
in aux heap (length_tas heap);;

(**Créant un tableau de int avec le codage d'hauffman (liste 0 et 1) a partir de l'arbre*)
let creaTabCheminHauff a =
  let rec creaAux a tab l = match a with
  |Feuille(b,_)->tab.(b)<-(List.rev l)
  |Node(_,g,d)->creaAux g tab (0::l);creaAux d tab (1::l)
in let res = (Array.make 257 []) in let _ = creaAux a (res) [] in res;;

(**Fontion qui écrit le code d'hauffman correspond a x dans output*)
let ecrireCodeHauff output enc x =
  let rec aux output l = match l with
  |[]->()
  |c::q->output_bit output c;aux output q
in aux output (enc.(x));;

(**Fonction qui encode un file a partir du tableau de reprsentation d'hauffman*)
let encodeFile file enc fileOut first=
  let rec aux input enc output = match input_bit_byte input with
      |256 -> ecrireCodeHauff output enc first
      |x -> ecrireCodeHauff output enc x;aux input enc output
  and input = open_in_bit file
  in aux input enc fileOut;close_in_bit input;;

(**Fonction qui creer la reprsentation de l'arbre d'hauffman au format demander*)
let representation_arbre a output =
  let rec aux a output = match a with
    |Feuille(l,_) -> if l < 255 then (output_bit output 0;output_bit_byte output l)
                     else if l = 255 then (output_bit output 0;output_bit_byte output 255; output_bit output 0)
                     else (output_bit output 0;output_bit_byte output 255; output_bit output 1)
    |Node(_,g,d) -> let _ = output_bit output 1 in let _ = aux g output in aux d output
in aux a output;;

(**Fonction qui ecrit un int correspondant a la somme des char modulo intMax*)
let md5write output md5 =
    let _ = output_bit_byte output 6 in
    let _ = output_bit_byte output 13 in
    let _ = output_bit_byte output 42 in
    let i4 = md5 mod 256 in
    let i3 = (md5 - i4) mod 65536 in (*Divise par 256*)
    let i2 = (md5 - i4 - i3) mod 16777216 in (*Divise par 65536*)
    let i1 = (md5 - i4 - i3 - i2) in(*Divise par 16777216*)
    let _  = output_bit_byte output (i1/16777216) in
    let _  = output_bit_byte output (i2/65536) in
    let _  = output_bit_byte output (i3/256) in
    output_bit_byte output i4;;

(**Fonction qui utilise tout les fonction presedante pour compresser un fichier de bout en bout*)
let compresseFile fileIn =
    if Sys.file_exists (fileIn^".hf") then raise (SystemFileFailComp ("Le fichier "^fileIn^".hf"^" existe déja\n")) else
    let output = (open_out_bit (fileIn^".hf")) in
    let _ = output_bit_byte output 135; output_bit_byte output 74; output_bit_byte output 31; output_bit_byte output 72;output_bit_byte output 0; in
    let tab = init() in
    let _,_,md5 = freqFile fileIn tab [] "" false in
    (*let tas,_ = creerTas tab 0 in
    let hauff = hauffManTas tas in*)
    let heap,_ = creerTasFibo tab 0 in
    let hauff = hauffMan heap in
    let _ = representation_arbre hauff output in
    let _ = encodeFile fileIn (creaTabCheminHauff hauff) output 256 in
    let _ = output_align_bit output in
    let _ = md5write output md5 in
    close_out_bit output;;


(*Fonction permettant de compresser l'arborescence des fichier*)
let rec freqArbo strTab tab =
    let freqString str tab =
      let rec aux str tab i n =
        if i = n then () else
        let x = Char.code (String.get str i) in
        let a,b = tab.(x) in tab.(x)<-(a,(b+1)); aux str tab (i+1) n
    in aux str tab 0 (String.length str)  in
    match strTab with
    |[]->()
    |str::sTab->freqString str tab; freqArbo sTab tab;;

(*Fonction permettant de compresser l'arborescence des fichier*)
let encodeArbo arbo enc output =
  let rec ecrireString str i n enc =
      if i = n then ecrireCodeHauff output enc 28 else
      let x = Char.code (String.get str i) in
      let _ = ecrireCodeHauff output enc x  in ecrireString str (i+1) n enc in
  let rec aux arbo enc = match arbo with
      |[]->()
      |str::sTab-> let _ = ecrireString str 0 (String.length str) enc in aux sTab enc
in aux arbo enc;;

(*Simulation d'encodage pour calculer la taille (nbre de bytes ignoré)*)
let simuleEncodeEntete arbo nb =
    let simuleEcrire taille enc x =
      let rec aux taille l = match l with
      |[]->taille
      |c::q->aux (taille+1) q
    in aux taille (enc.(x)) in
    let simuleEncodeArbo arbo enc =
      let rec ecrireString str i n enc taille=
          if i = n then simuleEcrire taille enc 28 else
          let x = Char.code (String.get str i) in
          let nTaille = simuleEcrire taille enc x in ecrireString str (i+1) n enc nTaille in
      let rec aux arbo enc taille = match arbo with
          |[]->taille
          |str::sTab-> let nTaille = ecrireString str 0 (String.length str) enc taille in aux sTab enc nTaille
    in aux arbo enc 0 in
        let tab = init() in
        let _ = freqArbo arbo tab in
        let _ = tab.(28)<-(28,nb) in
        (*let tas,_ = creerTas tab 0 in
        let hauff = hauffManTas tas in*)
        let heap,_= creerTasFibo tab 0 in
        let hauff = hauffMan heap in
        let taille = simuleRepresentation_arbre hauff in
        let nTaille = taille + simuleEncodeArbo arbo (creaTabCheminHauff hauff) in
        ((nTaille+7)/8,hauff);;


(**Fonction qui ecrit l'entete d'un dossier selon son type (Haufmaner ou non)*)
let ecritureEntete arbo taille2 output nb first dir=
    let mode = if first = 256 then (print_string "Perte de l'inter-operabilité \n";0) else 1 in
    let nTaille,hauff = simuleEncodeEntete arbo nb in
    let taille = if taille2<nTaille then taille2 else nTaille in
    if taille > (253-mode) then (Sys.remove (dir^".hf");close_out_bit output;raise (SystemFileFailComp ("Dossier "^dir^" avec chemin trop long \n")))
    else
    if taille = taille2 then
        let _ = output_bit_byte output (taille+2+mode) in
        let _ = output_bit_byte output 42 in
        let _ = output_bit_byte output (13+mode) in
        let _ = if mode = 1 then output_bit_byte output first in
        let rec writeString str i n output =
          if i = n then output_bit_byte output 28
          else let _ = output_bit_byte output (Char.code (String.get str i)) in writeString str (i+1) n output
        in let rec write arbo output = match arbo with
          |[]->()
          |s::l-> let _ = writeString s 0 (String.length s) output in write l output
        in write arbo output
    else
        let _ = output_bit_byte output (taille+2+mode) in
        let _ = output_bit_byte output 43 in
        let _ = output_bit_byte output (13+mode) in
        let _ = if mode = 1 then output_bit_byte output first in
        let _ = representation_arbre hauff output in
        let _ = encodeArbo arbo (creaTabCheminHauff hauff) output in
        output_align_bit output;;

(**Fonction qui utilise toutes les presedante pour compresser un dossier*)

let compresseDir dir =
    if length (Sys.readdir dir) = 0 then raise (SystemFileFailComp "Dossier Vide\n") else
    if Sys.file_exists (dir^".hf") then raise (SystemFileFailComp ("Le fichier "^dir^".hf"^" existe déja\n")) else
    let output = (open_out_bit (dir^".hf")) in
    let _ = output_bit_byte output 135; output_bit_byte output 74; output_bit_byte output 31; output_bit_byte output 72; in
    let tab = init() in let fifo = Queue.create () in
    let real,dirName = splitDirName dir in
    let _ = Queue.add (dirName^"/") fifo in
    let a,t,md5,nb = freqDir fifo tab [] 0 real 0 1 in
    (*let tas,first = creerTas tab nb in*)
    let heap,first = creerTasFibo tab nb in
    let _ = ecritureEntete a t output nb first dir in
    (*let hauff = hauffManTas tas in*)
    let hauff = hauffMan heap in
    let _ = representation_arbre hauff output in
    let crea = creaTabCheminHauff hauff in
    let rec encodeRec files path real= match files with
      |[]->()
      |s::l->if String.get s (String.length s - 1) = '/' then encodeRec l s real
             else let _ = encodeFile (real^path^s) crea output first in encodeRec l path real
in encodeRec a "" real;ecrireCodeHauff output crea 256;output_align_bit output; md5write output md5 ;close_out_bit output;;

let compression file =
  if Sys.is_directory file then compresseDir file
  else compresseFile file;;
