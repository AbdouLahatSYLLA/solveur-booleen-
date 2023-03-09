
   (* Projet solver booleenes 2021/2022 Programmation fonctionnel  :
   Binome : Abdou Lahat Sylla 12011836 et Yousra Mahi Moussa 12012194
   *)

type eb = V of int | VRAI | FAUX | AND of eb * eb | OR of eb * eb | XOR
          of eb * eb | NAND of eb * eb | NOT of eb ;;

let test = [(OR(V(1),V(2)),VRAI) ; (XOR(V(1),V(3)),V(2));(NAND(V(1),AND(V(2),V(3))),VRAI)];;
let rec contient e = function
  | [] -> false
  | t::q when t = e -> true
  | _::q -> contient e q
;;

let rec concatenation l1 l2 = match l1 with
    [] -> l2
  |x::ll1 -> x::(concatenation ll1 l2);;

let elimine_doublon l =
  let rec aux acc = function
    | [] -> List.rev acc
    | t::q when contient t acc -> aux acc q
    | t::q -> aux (t::acc) q in
  aux [] l

(** 1: determination de l enssemble des variables booleenes du systeme *)

(** fonction delete_exp qui fait ressortir les expression V(i) dans une operation (OR,AND,NOT,...) et renvoie la liste des V(i) *)
let rec delete_exp e = match e with
  |FAUX -> []
  |V(i) -> [e]
  |AND(x,y) ->  delete_exp x  @ delete_exp y
  |XOR(x,y) ->  delete_exp x  @ delete_exp y
  |NAND(x,y)->  delete_exp x  @ delete_exp y
  |NOT x -> delete_exp x
  |VRAI -> []
  |OR(x,y) ->  delete_exp x  @ delete_exp y;;

(* fonction extraire_var qui extrait dans un systeme donné en argument tous les variable booleenes V(i) et renvoie la liste de ces variables *)
let rec extraire_var sys = match sys with
  |[] -> []
  |(l,s)::v  -> elimine_doublon (concatenation (delete_exp l @ delete_exp s) (extraire_var v))
;;

(*let variable = extraire_var test;;*)

(** 2: generation des environnement possibles *)

let rec remplir_resultat listVar n = match n with
    0 -> [[]]
  |_ -> match listVar with
      [] -> [[]]
    |u::v -> let x = remplir_resultat listVar (n-1) in
        List.concat(List.map (fun x -> List.map (fun listVar -> listVar@x)listVar)x)
;;
(*fonction pour faire les combinaisons des valeur de verité *)
let rec combinaison var list = match list with [] -> [] | u :: v -> List.combine var u :: (combinaison var v) ;;

(*fonction pour remplir la table de verité *)
(*let table = remplir_resultat ([[VRAI];[FAUX]]) (List.length variable);;*)

(*let environnement = combinaison variable table;;*)

(** 3)  evaluation de la satisfaction d une equation donné dans un environnement donnée *)

let rec equal l v = match (l,v) with
    ([],[]) -> true
  |([],l) -> false
  |(l,[]) -> false
  |((w::x),(y::z)) -> if List.length l != List.length v then false else if w=y then equal x z else false
;;

let rec supprimerVide v = match v with
    []::_ -> []
  |[] -> []
  | (x::y) :: li -> if equal (x::y) [] then supprimerVide  li else (x::y) :: supprimerVide li ;;

let rec valassocie var env =  match  env with
    [] -> raise(Not_found)
  |(l,s)::v -> if l = var then s else (valassocie var v )
;;

let eval_and  l s =  if l = VRAI then s else FAUX;;
let eval_or l s = if l = VRAI then VRAI else s;;
let eval_xor l s = if l != s then VRAI else FAUX;;
let eval_not l = if l = VRAI then FAUX else VRAI;;
let eval_nand l s = eval_not (eval_and l s);;

let rec app_env e env = match e with
    FAUX -> FAUX
  |VRAI -> VRAI
  |V(i) -> valassocie e  env
  |AND(x,y) ->  eval_and (app_env x env)   (app_env y env)
  |XOR(x,y) ->  eval_xor (app_env x env)   (app_env y env)
  |NAND(x,y)->  eval_nand (app_env x env)   (app_env y env)
  |NOT x -> eval_not (app_env x env)
  |OR(x,y) ->  eval_or (app_env x env )   (app_env y env)
;;
(*fonction qui verifie les solution V(i) dans un sous environnement*)
let rec solver sys env = match sys with
    [] -> env
  |(l,s)::v -> let x = app_env l env in let y = app_env s env in if x=y then solver v env else []
;;

let rec solution sys env = match env with
    [] -> []
  |e::x -> ( supprimerVide [solver sys e]) @ ( supprimerVide (solution sys x))
;;

(** fonction pour resoudre tout systeme *)
let resolver sys = solution sys (combinaison (extraire_var sys) (remplir_resultat ([[VRAI];[FAUX]]) (List.length (extraire_var sys)) ) ) ;;



resolver [(OR(V(1),V(2)),FAUX) ; (XOR(V(1),V(3)),V(2));(NAND(V(1),AND(V(2),V(3))),VRAI)] ;;
- : (eb * eb) list list = [[(V 1, FAUX); (V 2, FAUX); (V 3, FAUX)]]
(** exemple  de cas ou on a une seule solution*)
resolver [(OR(V(1),V(2)),VRAI) ; (XOR(V(1),V(3)),V(2));(NAND(V(1),AND(V(2),V(3))),VRAI)] ;;
- : (eb * eb) list list =
[[(V 1, FAUX); (V 2, VRAI); (V 3, VRAI)];
 [(V 1, VRAI); (V 2, FAUX); (V 3, VRAI)];
 [(V 1, VRAI); (V 2, VRAI); (V 3, FAUX)]]
 (* le systeme donné avec le sujet la solution est la bonne *)
resolver [(OR(V(1),V(2)),FAUX) ; (XOR(V(1),V(3)),V(2));(NAND(V(1),AND(V(2),V(3))),FAUX)] ;;
- : (eb * eb) list list = [] (*dans ce cas on a Pas de solution pour ce systeme*)