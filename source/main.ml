open Decompression;;
open Compression;;
open Unix;;

let end_withHF name =
    if (String.compare ".hf" (String.sub name ((String.length name) -3) 3) )== 0 then true
    else raise (SystemFileFailDec ("Le fichier "^name^" ne fini pas par .hf\n"))
;;

let main =
  let rec run indice mode argc =
    try begin
        if indice == argc then ()
        else if mode == 1 && end_withHF Sys.argv.(indice) && Sys.file_exists Sys.argv.(indice) && not (Sys.is_directory Sys.argv.(indice))then (decompression (Sys.argv.(indice)); run (indice+1) mode argc)
        else if mode == 0 && Sys.file_exists Sys.argv.(indice) then (compression (Sys.argv.(indice)); run (indice+1) mode argc)
        else raise (SystemFileFailComp ("Le fichier "^Sys.argv.(indice)^" n'existe pas ou non compatible (pas <.hf/dossier> pour -d)\n"))
      end
    with
    |SystemFileFailComp str -> (print_string str; run (indice +1) mode argc)
    |SystemFileFailDec str -> (print_string str; run (indice +1) mode argc)
  in
  let argc = Array.length (Sys.argv) in
  if argc < 2
    then (print_string "usage : \n compression : hauff [file...]\n decompression : hauff -d [file.hf...] \n";
         exit 0)
  else
    let mode = if (String.compare Sys.argv.(1) "-d") == 0 then 1 else 0 in
    if argc == mode + 1 then (print_string "usage : \n compression : hauff [file...]\n decompression : hauff -d [file.hf...] \n";
                              exit 0)
    else run (mode+1) mode argc; exit(0);;

let () = main;;
