open Struct;;
open Bitio;;
open Unix;;

exception SystemFileFailDec of string;;

(**Fonction remplasant le .hf*)
let rename file =
    String.sub file 0 ((String.length file)-3)
;;

(** Fonction prenant en argument le chemin d'un fichier et renvoyant un tuple(relativePath,Name)  *)
let splitDirName file =
    let rec aux i j n file =
    if i = n then j
    else
        match String.get file i with
            |'/'-> aux (i+1) (i+1) n file
            |_-> aux (i+1) j n file
    in let j = aux 0 0 (String.length file) file
in ((String.sub file 0 j),(String.sub file j ((String.length file) - j)))
;;

(**Fonction decodant l'input a l'aide de l'arbre a dans le fichier name*)
let decode name input a sep =
    if Sys.file_exists name then raise (SystemFileFailDec ("Le fichier "^name^" existe déja\n"))
    else
        let rec read ai a input output md5 = match input_bit input,a with
            |0,Node(_,Feuille(256,_),_) -> md5
            (*|0,Node(_,Feuille(28,_),_) -> if booleanDir then md5 else (output_bit_byte output 28;read ai ai input output ((md5+28) mod 1073741824))*)
            |0,Node(_,Feuille(x,_),_) -> if x = sep then md5
                else (output_bit_byte output x;read ai ai input output ((md5+x) mod 1073741824))
            |0,Node(_,g,_) -> read ai g input output md5
            |1,Node(_,_,Feuille(256,_))-> md5
            (*|1,Node(_,_,Feuille(28,_))-> if booleanDir then md5 else (output_bit_byte output 28;read ai ai input output ((md5+28) mod 1073741824))*)
            |1,Node(_,_,Feuille(x,_)) -> if x = sep then md5
                else (output_bit_byte output x;read ai ai input output ((md5+x) mod 1073741824))
            |1,Node(_,_,d) -> read ai d input output md5
            |_,_ -> md5
        and output = open_out_bit (name)
in let md5 = read a a input output 0 in close_out_bit output;md5
;;

(**Fonction recuperant l'arbre encoder dans input*)
let getArbre input =
    let rec aux input = match input_bit input with
        |1 -> let g,nbG = aux input in let d,nbD = aux input in Node(0,g,d),(nbG+nbD+1)
        |0 -> let x = input_bit_byte input in
            if x < 255 then Feuille(x,0),9
            else if input_bit input = 0 then Feuille(255,0),10
            else Feuille(256,0),10
        |x -> failwith "Hey erreur bizarre"
in aux input
;;


(**Fonction verifiant que le fichier est bien une de nos archive*)
let checkBitMagique input =
    if
        input_bit_byte input = 135 &&
        input_bit_byte input = 74 &&
        input_bit_byte input = 31 &&
        input_bit_byte input = 72
    then true
    else false
;;

(**Fonction ignorant i byte de input*)
let ignore_N_Byte_Decode input i =
    let rec aux input j i =
        if j<i then
            let _ = input_bit_byte input in aux input (j+1) i
in aux input 0 i
;;

(**Fonction recuperant l'arborescence des fichier si non compresser*)
let get_files_names_non_compress input size =
    let rec r input tab chaine size = match input_bit_byte input with
        | 28 -> if size = 0
            then tab@[chaine] (* reverse liste, add, reverse liste*)
            else r input (tab@[chaine]) "" (size -1)
        | x -> r input tab (chaine^Char.escaped (Char.chr x)) (size -1)
in r  input [] "" (size -1)
;;

(**Fonction recuperant l'arborescence des fichier si compresser*)
let get_files_names_compress input n =
    let a, nbignore= getArbre input in
    let rec read ai a input str i= match input_bit input,a with
        |0,Node(_,Feuille(28,_),_) -> str,(i+1)
        |0,Node(_,Feuille(x,_),_) -> read ai ai input (str^Char.escaped (Char.chr x)) (i+1)
        |0,Node(_,g,_) -> read ai g input str (i+1)
        |1,Node(_,_,Feuille(28,_))-> str,(i+1)
        |1,Node(_,_,Feuille(x,_))-> read ai ai input (str^Char.escaped (Char.chr x)) (i+1)
        |1,Node(_,_,d) -> read ai d input str (i+1)
        |_,_ -> str,(i+1)
    in let rec createArbo input a i n arbo =
        if (nbignore+i+7)/8 = n then arbo else
            let str,nI = read a a input "" 0 in
            let nArbo = List.rev (str::(List.rev arbo))
            in createArbo input a (i+nI) n nArbo
in let arbo = createArbo input a 0 n [] in input_align_bit input;arbo
;;

(**Fonction decodant un repertoire et creer l'arborescence si besoin*)
let sub_decompress_rep files_names arbre input path sep =
    let rec dec dir_name files_names arbre input md5=  match files_names with
    | [] -> md5
    | t::q -> if String.get t ((String.length t) -1) = '/'
        then if not (Sys.file_exists (path^t)) then let _ = mkdir (path^t) 0o750 in dec t q arbre input md5
            else dec t q arbre input md5
        else let md = decode (path^dir_name^t) input arbre sep in dec dir_name q arbre input ((md5+md) mod 1073741824)
in dec "" files_names arbre input 0;;




(**Fonction ignorant le EOF dans le cas d'une décomprssion de repertoire*)
let rec ignore_EOF ai a input = match input_bit input,a with
    |0,Node(_,Feuille(256,_),_) -> ()
    |0,Node(_,Feuille(x,_),_) -> ignore_EOF ai ai input
    |0,Node(_,g,_) -> ignore_EOF ai g input
    |1,Node(_,_,Feuille(256,_))-> ()
    |1,Node(_,_,Feuille(x,_))-> ignore_EOF ai ai input
    |1,Node(_,_,d) -> ignore_EOF ai d input
    |_,_ -> ()
;;

(**Fonction utilsant les fonction presedante pour decoder un repertoire*)
let decompress_rep input i path ext sep=
    let files_names =
        if ext = 1 then get_files_names_non_compress input i
        else get_files_names_compress input i
    in let arbre,_ = getArbre input
    in let md5 = sub_decompress_rep files_names arbre input path sep
    in let _ = ignore_EOF arbre arbre input
in md5
;;


(**Fonction utilisant les presedante pour decoder un fichier*)
let decompress_file input file  =
    let arbre,_ = getArbre input
in decode (rename file) input arbre 256
;;
(**Fonction permettant de determiner de quel type est l'archive*)
let checkExtensionEntete input i =
    if i = 0 then 0,256
    else if i>2 then
        let i1 = input_bit_byte input in
            if i1 = 42 then
                let i2 = input_bit_byte input in
                if i2 = 13 then 1,256
                else if i2 = 14 then 1,(input_bit_byte input)
                else let _ = ignore_N_Byte_Decode input (i-2) in 0,256
            else if i1 = 43 then
            let i2 = input_bit_byte input in
            if  i2 = 13 then 2,256
            else if i2 = 14 then 2,(input_bit_byte input)
            else let _ = ignore_N_Byte_Decode input (i-2) in 0,256
        else let _ = ignore_N_Byte_Decode input (i-1) in 0,256
    else let _ = ignore_N_Byte_Decode input i in 0,256
;;


(**Fonction permettant de verifiant si le fichier contient l'extension md5*)
let checkExtensionFin input =
    let _ = input_align_bit input in
    let i = input_bit_byte input in
    if i = 0 then false
    else if i>2 then
        if input_bit_byte input = 13 then
            if input_bit_byte input = 42 then true
            else let _ = ignore_N_Byte_Decode input (i-2) in false
        else let _ = ignore_N_Byte_Decode input (i-1) in false
    else let _ = ignore_N_Byte_Decode input i in false
;;


(**Fonction permettant de verifiant que la Decompression c'est bien passer*)
let md5check input md5 file =
    let i4 = input_bit_byte input in
    let i3 = input_bit_byte input in
    let i2 = input_bit_byte input in
    let i1 = input_bit_byte input in
    if md5 = i4*16777216+i3*65536+i2*256+i1 then ()
    else print_string ("HashCode non cohérant "^file^" probablement corrompu");;

(**Fonction decodant une archive file en utilisant les presedante*)
let decompression file =
    let path,_ = splitDirName file in
    let aux  input =
    if not (checkBitMagique input) then raise (SystemFileFailDec ("Erreur fichier "^file^" non compatible \n"))
    else let i = input_bit_byte input in
        let ext,sep = checkExtensionEntete input i in
        if ext != 0 && sep = 256 then decompress_rep input (i-2) path ext sep
        else if ext != 0 && sep != 256 then decompress_rep input (i-3) path ext sep
        else decompress_file input file
in let input = open_in_bit file
in let md5 = aux input in
    if checkExtensionFin input then (md5check input md5 path;close_in_bit input)
    else close_in_bit input
;;
