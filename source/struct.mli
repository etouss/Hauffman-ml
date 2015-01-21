type 'a tree =
| Feuille of 'a
| Node of int * 'a tree * 'a tree

type heap

(** Fonction creer le tas de fibo le renvoi accompagné de l'octet seperateur de fichier *)
val creerTasFibo : (int * int) array -> int -> heap * int

(** Fonction recupere le minimum du tas et retire ces connexion *)
val extract_min : heap -> int

(** Fonction a inserting_node sauf qu'elle remet a 0 les connexion *)
val inserting_node2 : heap -> int -> (int * int) tree -> unit

val recupKey_val: heap -> int -> (int * int) tree

val length_tas: heap -> int


val entasserMinTas : ('a * int) tree array -> int -> int -> ('a * int) tree array

val extractionMinTas : ('a * int) tree array -> int -> ('a * int) tree

val extractionMinTas2 : 'a array -> int -> 'a

val creerTas : (int * int) array -> int -> (int * int) tree array * int
