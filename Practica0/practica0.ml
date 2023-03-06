(* EJERCICIO 1*)

(* mapdoble (function x -> x) (function x -> -x) [1;1;1;1;1];; *)

let rec mapdoble f1 f2 = function
  [] -> []
  | hd::[] -> (f1 hd)::[]
  | hd1::hd2::tl -> (f1 hd1)::(f2 hd2)::(mapdoble f1 f2 tl)
;;

(*Indique el tipo de la función mapdoble:
val mapdoble : ('a -> 'b) -> ('a -> 'b) -> 'a list -> 'b list = <fun> *)

(*Indique el valor de:
 mapdoble (function x -> x*2) (function x -> "x") [1;2;3;4;5];; 
 Error: This expression has type string but an expression was expected of type int *)

 (*Indique el tipo de:
 let y = function x -> 5 in mapdoble y;;
 - : ('_weak1 -> int) -> '_weak1 list -> int list = <fun> *)


 (* EJERCICIO 2*)

 let rec primero_que_cumple predicado = function
  | [] -> raise (Not_found)
  | hd::tl -> if (predicado hd) then hd else primero_que_cumple predicado tl
 ;;

 (* Indique el tipo de la función primero_que_cumple
   val primero_que_cumple : ('a -> bool) -> 'a list -> 'a = <fun> *)

let existe predicado list = 
  try primero_que_cumple predicado list with
   Not_found -> false
  | _ -> true
;;

let asociado list f =
  match list with
  [] -> raise Not_found
  | hd::tl -> snd(primero_que_cumple (function(a,b) -> if a = f then true else raise (Not_found)) list)
;;


(* EJERCICIO 3*)

type 'a arbol_binario =
  Vacio
  | Nodo of 'a * 'a arbol_binario * 'a arbol_binario
;;

(* # let a1 = Nodo(3, Nodo(2,Vacio,Vacio), Nodo(5,Nodo(4,Vacio,Vacio),Nodo(1,Vacio,Vacio)));;
val a1 : int arbol_binario =
  Nodo (3, Nodo (2, Vacio, Vacio),
   Nodo (5, Nodo (4, Vacio, Vacio), Nodo (1, Vacio, Vacio))) *)

(* val ... : 'a arbol_binario -> 'a list = <fun> *)

(* in_orden: subárbol izq, raíz y subárbol dcho*)
let rec in_orden = function
  Vacio -> []
  | Nodo (valor, izq, dcha) -> (in_orden izq) @ [valor] @ (in_orden dcha)
;;
(*  # in_orden a1;;
- : int list = [2; 3; 4; 5; 1]
   *)


(* pre_orden: raíz, subárbol izquierdo, subárbol derecho.*)
let rec pre_orden = function
  Vacio -> []
  | Nodo (valor, izq, dcha) -> [valor] @ (pre_orden izq) @ (pre_orden dcha)
;;

(* # pre_orden a1;;
- : int list = [3; 2; 5; 4; 1] *)

(* post_orden: subárbol izquierdo, subárbol derecho, raíz*)
let rec post_orden = function
    Vacio -> []
    | Nodo (valor,izq,dcha) -> post_orden izq @ post_orden dcha @ [valor]
;;

(* # post_orden a1;;
- : int list = [2; 4; 1; 5; 3] *)

(* anchura: cada nodo del nivel antes de ir al nivel inferior *)
let anchura arbol = 
  let rec aux a_visitar visitados = match a_visitar with
      [] -> List.rev visitados
      | Vacio::tl -> aux tl visitados
      | Nodo(valor, izq, dcha)::tl -> aux (tl@[izq]@[dcha]) (valor::visitados)
  in aux [arbol] [];;

(*  # anchura a1;;
- : int list = [3; 2; 5; 4; 1]  
*)


(* EJERCICIO 4 *)

type 'a conjunto = Conjunto of 'a list;;
let conjunto_vacio = Conjunto [];;

(* val pertenece : 'a -> 'a conjunto -> bool = <fun> *)
let rec pertenece a (Conjunto c) = match c with
   [] -> false
  | (head::tail) -> if (head = a) then true else pertenece a (Conjunto tail)
;;
(* pertenece 1 (Conjunto [1;2;3]);;
- : bool = true
# pertenece 1 (Conjunto [2;2;3]);;
- : bool = false
# pertenece 1 (Conjunto []);;
- : bool = false
   *)

(* val agregar : 'a -> 'a conjunto -> 'a conjunto = <fun> *)
let agregar a (Conjunto c) = 
  if(pertenece a (Conjunto c)) then (Conjunto c)
  else Conjunto (c @ [a])
;;

(* # agregar 1 (Conjunto []);;
- : int conjunto = Conjunto [1]
# agregar 1 (Conjunto [1;2;3]);; 
- : int conjunto = Conjunto [1; 2; 3] *)

(* val conjunto_of_list : 'a list -> 'a conjunto = <fun> *)
let conjunto_of_list l =
	let rec aux (Conjunto c) = function
		| [] -> (Conjunto c)
		| hd::tl -> aux (agregar hd (Conjunto c)) tl
	in aux conjunto_vacio l
;;

(* # conjunto_of_list [];;
- : 'a conjunto = Conjunto []
# conjunto_of_list [1;2;3];;
- : int conjunto = Conjunto [3; 2; 1]
 *)

(* val suprimir : 'a -> 'a conjunto -> 'a conjunto = <fun> *)
let suprimir a (Conjunto c) =
	let rec aux list conj = match conj with
		| Conjunto (h::t) -> if a=h then Conjunto (list@t) else aux (h::list) (Conjunto t)
		| Conjunto [] -> Conjunto c
	in aux [] (Conjunto c)
;;

(* cardinal : 'a conjunto -> int, número de elementos de un conjunto *)
let cardinal (Conjunto c) =
	let rec count a = function
		[] -> a
		|_::t -> count(a+1) t
		in count 0 c
;;

(* union : 'a conjunto -> 'a conjunto -> 'a conjunto *)
let union (Conjunto c1) (Conjunto c2) =			
	let rec agregar_elementos conj1 conj2 = match conj2 with
		[] -> (Conjunto conj1)
		| h::t -> if (pertenece h (Conjunto conj1)) then agregar_elementos conj1 t
			     else agregar_elementos (h::conj1) t
	in agregar_elementos c1 c2;;

(* interseccion : 'a conjunto -> 'a conjunto -> 'a conjunto *)
let interseccion (Conjunto c1) (Conjunto c2) =
  let rec f final conj1 = match conj1 with
    [] -> Conjunto final
    | h::t -> if (pertenece h (Conjunto c2)) then f (h::final) t
                else f final t
  in f [] c1;;

(*interseccion (Conjunto [1; 2; 3]) (Conjunto [2; 3; 4]);
  interseccion (Conjunto [1; 2; 3]) conjunto_vacio;*)

(* diferencia : 'a conjunto -> 'a conjunto -> 'a conjunto, todos los elementos del conj1 que no están en conj2 *)
let diferencia (Conjunto c1) (Conjunto c2) =
  let rec f aux conj1 = match conj1 with
    [] -> Conjunto aux
    | h1::t1 -> if (pertenece h1 (Conjunto c2)) then f aux t1
                else f (h1::aux) t1
  in f [] c1;;
                         
(* incluido : 'a conjunto -> 'a conjunto -> bool, conj1 tiene todos sus elementos en conj2 *)
let incluido (Conjunto c1) (Conjunto c2) =
  let rec f conj1 conj2 = match conj1 with
    [] -> true
    | h1::t1 -> if (pertenece h1 (Conjunto c2)) then f t1 conj2
                else false
  in f c1 c2;;

(* igual : 'a conjunto -> 'a conjunto -> bool *)
let igual (Conjunto c1) (Conjunto c2) = 
	if((diferencia (Conjunto c1) (Conjunto c2))= Conjunto []) then true else false;;

(* producto_cartesiano : 'a conjunto -> 'b conjunto -> ('a * 'b) conjunto *)
let producto_cartesiano (Conjunto c1) (Conjunto c2) = 
	let rec f aux conj1 conj2 = match conj1,conj2 with
		[],_ -> Conjunto (aux)                            (* primer conjunto vacio *)
		| h1::_,h2::t2 -> f ((h1,h2)::aux) conj1 t2       (* ambos conjuntos con elementos *)
		| _::t1,[] -> f aux t1 c2                         (* segundo conjunto vacio *)
	in f [] c1 c2;;
	
(* list_of_conjunto : 'a conjunto -> 'a list *)	
let list_of_conjunto (Conjunto c) = c;;