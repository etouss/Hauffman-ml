(* This code was written by Juliusz Chroboczek.  MIT license. *)

(* Flot de bits en lecture *)
type bit_in_channel

(* Flot de bits en écriture *)
type bit_out_channel

(* Ouvre un flot en lecture *)
val open_in_bit : string -> bit_in_channel

(* Ouvre un flot en écriture *)
val open_out_bit : string -> bit_out_channel

(* Lit un bit *)
val input_bit : bit_in_channel -> int

(* Lit huit bits *)
val input_bit_byte : bit_in_channel -> int

(* Lit et ignore entre 0 et 7 bits, de façon à aligner la position courante *)
val input_align_bit : bit_in_channel -> unit

(* Écrit un bit *)
val output_bit : bit_out_channel -> int -> unit

(* Écrit huit bits *)
val output_bit_byte : bit_out_channel -> int -> unit

(* Écrit entre 0 et 7 bits, de façon à aligner la position courante *)
val output_align_bit : bit_out_channel -> unit

(* Ferme un flot en lecture, ignore la fin du fichier *)
val close_in_bit : bit_in_channel -> unit

(* Ferme un flot en écriture, peut écrire de 0 à 7 bits de zéros *)
val close_out_bit : bit_out_channel -> unit
