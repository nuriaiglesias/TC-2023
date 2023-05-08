(* Nuria Iglesias - n.iglesias@udc.es*)

# #load "talf.cma";;
# open Conj;;
# open Auto;;
# open Ergo;;
# open Graf;;

(* Ejercicio 1*)

let g1 = gic_of_string "S A B C D; a b c d; S; S -> A B | C D; A -> a; B -> b; C -> c; D -> d;";;
let g2 = gic_of_string "S A B C; a b c d; S; S -> A B | C d; A -> a; B -> b; C -> c;";;

let g3 = gic_of_string "S A B C; a b; S; S -> A B | B C; A -> B A | a; B -> C C | b; C -> A B | a;";;
let c1 = cadena_of_string "b a a b a";;
let c2 = cadena_of_string "a b b";;
  
let es_fnc (Gic (noterminal, terminal, regla, inicial)) =
  let rec loop = function
    Conjunto [] -> true
    (* Comprobamos que sean símbolos no terminales válidos *)
    (* S -> A B *)
  | Conjunto (Regla_gic (simbolo, [No_terminal m; No_terminal k])::tl) ->
    if (not (pertenece (No_terminal m) noterminal) || not (pertenece (No_terminal k) noterminal)) then false
    else loop (Conjunto tl)
    (* Comprobamos que sea símbolo terminal válido *)
    (* S -> a *)
  | Conjunto (Regla_gic (simbolo, [Terminal c])::tl) ->
    if not (pertenece (Terminal c) terminal) then false
    else loop (Conjunto tl)
  | _ -> false
  in loop regla;;


(* EJERCICIO 2 *)

(* Alg CYK - verifica si cadena pertenece a gramatica *)
let cyk cadena gramatica =
    let long_cadena = List.length cadena in
    (* Comprobación cadena no vacía - lenguaje en forma fnc *)
    if long_cadena = 0 then raise (Invalid_argument "La cadena no puede ser vacía.")
    else if not (es_fnc gramatica) then raise (Invalid_argument "La gramática no es FNC.")
    else
      let matriz = Array.make_matrix long_cadena long_cadena (Conjunto []) in
      let (Gic (_,_,regla,_)) = gramatica in 
       (* Convertimos conjunto en lista *)
      let reglas = list_of_conjunto regla in 
      (* Recorremos columnas de la matriz = tamaño de la cadena - 1 *)
      for columna = 0 to long_cadena-1 do
        (* Recorremos la cadena *)
        let simb_cad = List.nth cadena columna in
        let alcanzable simb_cad = match simb_cad with
            (* Comprobamos que no terminales pueden alcanzar elementos de cadena*)
          | Terminal terminal ->
            let alcanzados = 
              (* Filtro y guardo los resultados *)
              List.filter (function Regla_gic(_, [Terminal t]) -> terminal = t | _ -> false) reglas in
            List.map (fun (Regla_gic(alcanzados, _)) -> alcanzados) alcanzados 
            (* Simbolo es un no terminal *)
          | _ -> raise (Invalid_argument "La cadena contiene no terminales.")
        in matriz.(0).(columna) <- Conjunto (alcanzable simb_cad)
      done;  
      (* Recorremos matriz, calculamos valores tabla *)
      for fila = 1 to long_cadena-1 do
        for columna = 0 to long_cadena-1-fila do
          for k = 0 to fila-1 do
            (* Producto cartesiano de dos celdas anteriores *)
            let no_term1 = matriz.(k).(columna) in
            let no_term2 = matriz.(fila-k-1).(columna+k+1) in
            let no_terms = list_of_conjunto (cartesiano no_term1 no_term2) in
            let result = 
              List.map ( fun (no_t1,no_t2) -> 
                  (* Busca reglas con cuerpo no_t1 y no_t2 y devuelve los no terminales del lado izq *)
                let alcanzable = function
                  | (nt1,nt2) ->
                    let rules = List.filter (function Regla_gic(_, l_no_terms) -> l_no_terms = [nt1;nt2]) reglas in
                    List.map (fun (Regla_gic(no_t, _)) -> no_t) rules 
                in alcanzable (no_t1,no_t2)
              ) no_terms
              (* Agregamos resultados de alcanzable *)
            in matriz.(fila).(columna) <- union (matriz.(fila).(columna)) (Conjunto (List.concat result));
          done
        done
      done;  
      (* Última comprobación *)
      pertenece (No_terminal "S") matriz.(long_cadena-1).(0)
    ;;