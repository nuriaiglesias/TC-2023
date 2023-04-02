(*# load "talf.cma";;*)
open Conj;;
open Auto;;
open Ergo;;
open Graf;;

(* EJEMPLOS *)

(* ES AFNE *)
let a1 = af_of_string "0 1 2 3; a b c; 0; 1 3; 0 1 a; 1 1 b; 1 2 a; 2 0 epsilon; 2 3 epsilon; 2 3 c;";; 

(* ES AFN *)
let a2 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"],
Conjunto [Terminal "a"; Terminal "b"],
Estado "0",
Conjunto [Arco_af (Estado "0", Estado "0", Terminal "b");
          Arco_af (Estado "0", Estado "1", Terminal "a");
          Arco_af (Estado "0", Estado "0", Terminal "a");
          Arco_af (Estado "1", Estado "2", Terminal "b");
          Arco_af (Estado "2", Estado "3", Terminal "b");
          Arco_af (Estado "3", Estado "4", Terminal "a");
],
Conjunto [Estado "4"]);;

(* ES ADF *)
let a3 = Af (Conjunto [Estado "0"; Estado "01"; Estado "02"; Estado "03"; Estado "014"],
Conjunto [Terminal "a"; Terminal "b"],
Estado "0",
Conjunto [Arco_af (Estado "0", Estado "01", Terminal "a");
          Arco_af (Estado "0", Estado "0", Terminal "b");
          Arco_af (Estado "01", Estado "01", Terminal "a");
          Arco_af (Estado "01", Estado "02", Terminal "b");
          Arco_af (Estado "02", Estado "01", Terminal "a");
          Arco_af (Estado "02", Estado "03", Terminal "b");
          Arco_af (Estado "03", Estado "014", Terminal "a");
          Arco_af (Estado "03", Estado "0", Terminal "b");
          Arco_af (Estado "014", Estado "01", Terminal "a");
          Arco_af (Estado "014", Estado "02", Terminal "b");
],
Conjunto [Estado "014"]);;

(* AFN y ADF son equivalentes *)

(* Más ejemplos para equivalentes *)
let eq1 =  af_of_string "0 1 2 3 4 5 6; a b; 0; 3 6; 0 1 epsilon; 0 4 epsilon; 1 2 a; 2 3 b; 3 3 a; 3 3 b; 4 4 a; 4 4 b; 4 5 a; 5 6 b;";;
let eq2 =  af_of_string "0 1 2 3 4 5 6; a b; 0; 3 6; 0 2 a; 0 4 a; 0 4 b; 0 5 a; 2 3 b; 1 2 a; 3 3 a; 3 3 b; 4 4 a; 4 4 b; 4 5 a; 5 6 b;";;
let eq3 =  af_of_string "0 245 346 345 34 45 46 4; a b; 0; 346 345 34 46; 0 245 a; 0 4 b; 245 346 b; 245 45 a; 346 345 a; 346 34 b; 345 345 a; 345 346 b; 34 345 a; 34 34 b; 45 45 a; 45 46 b; 46 45 a; 46 4 b; 4 45 a; 4 4 b;";;


let eq4 = af_of_string "0 1 2 3 4 ; a b; 0; 4; 0 0 b; 0 0 a; 0 1 a; 1 2 b; 2 3 b; 3 4 a;";;
let eq5 = af_of_string "0 01 02 03 014 ; a b; 0; 014; 0 01 a; 0 0 b; 01 01 a; 01 02 b; 02 01 a; 02 03 b; 03 014 a; 03 0 b; 014 01 a; 014 02 b;";;

(* EJERCICIO 1 *)

  let es_afne (Af (_,_,_,arcs,_)) =
    let rec loop = function
      Conjunto ((Arco_af(_,_,terminal))::tl) ->
        if terminal = (Terminal "") then
          true
        else
          loop (Conjunto tl)
      | Conjunto _ -> false
    in loop arcs
  ;;

  let es_afn (Af (_,_,_,arcs,_)) =
    let rec loop cc boolean = function
      Conjunto ((Arco_af(s1,_,terminal))::tl) ->
        if terminal = (Terminal "") then
          loop cc boolean (Conjunto(tl))
        else if pertenece (s1,terminal) cc then
          loop (agregar (s1,terminal) cc) true (Conjunto(tl))
        else
          loop (agregar (s1,terminal) cc) boolean (Conjunto(tl))
      | Conjunto _ -> boolean
    in loop (Conjunto []) false arcs
  ;;

  let tiene_uno (estado,simbolo) transiciones =
    let rec recorrer acc = function
      | Conjunto [] -> acc = 1
      | Conjunto (Arco_af (e,_, s)::tl) when estado=e && simbolo=s && s<>(Terminal "") && s<>(Terminal "epsilon")->
          (acc > 1) || recorrer (acc+1) (Conjunto tl)
      | Conjunto (Arco_af _::tl) -> 
          recorrer acc (Conjunto tl)
    in recorrer 0 transiciones;;

  let es_afd (Af (estados,simbolos,_,transiciones,_)) =
    let rec recorrer_estados = function
      | Conjunto [] -> true
      | Conjunto ((Estado est)::estado_tl) ->
        let rec recorrer_simbolos = function
          | Conjunto [] -> true
          | Conjunto ((Terminal s)::simbolo_tl) -> 
              if (tiene_uno (Estado est, Terminal s) transiciones) then
                recorrer_simbolos (Conjunto simbolo_tl)
              else
                false
          | Conjunto ((No_terminal s)::_) -> 
              false
        in recorrer_simbolos simbolos && recorrer_estados (Conjunto estado_tl)
    in recorrer_estados estados;;

  (* EJERCICIO 2 *)

  let rec transition estado value (Conjunto arcoAf) = match arcoAf with 
      [] -> estado
    | Arco_af(e,e2,sym)::t -> if e = estado && sym = value then 
                                if (sym <> Terminal "") && (e = e2) then 
                                  transition estado value (Conjunto t)
                                else 
                                  e2
                              else transition estado value (Conjunto t)
;;


let equivalentes (Af(_,simbolos1, inicial1, arcos1, finales1)) (Af(_, simbolos2, inicial2,arcos2, finales2)) =
  let alfabeto = agregar (Terminal "") (union simbolos1 simbolos2) in 
  let rec loop (Conjunto cola) visitados =  match cola with
      [] -> true
    | (estadoAct1, estadoAct2)::t ->  if pertenece (estadoAct1, estadoAct2) visitados then 
                  loop (Conjunto t) visitados
                else if (pertenece estadoAct1 finales1 && not (pertenece estadoAct2 finales2)) 
                || (not (pertenece estadoAct1 finales1) && pertenece estadoAct2 finales2) then 
                  false
                else
                  let vistos1 = agregar (estadoAct1, estadoAct2) visitados in 
                  let rec loopAux (Conjunto alf) vistos= match alf with
                        [] -> true
                      | a::l -> let nuevoEtd1 = transition estadoAct1 a arcos1 in 
                                let nuevoEtd2 =  transition estadoAct2 a arcos2 in
                                if (not (pertenece (nuevoEtd1, nuevoEtd2) vistos)) then
                                  if (a<>(Terminal "") && (nuevoEtd1 = estadoAct1 || nuevoEtd2 = estadoAct2)) then 
                                    loopAux (Conjunto l)  vistos 
                                  else 
                                    loop (agregar (nuevoEtd1, nuevoEtd2) (Conjunto cola)) vistos 
                                else loopAux (Conjunto l)  vistos 
                  in loopAux alfabeto vistos1
  in loop (Conjunto [(inicial1,inicial2)])  (Conjunto []) 
;;


  (* EJERCICIO 3 *)

  let escaner_afn cadena (Auto.Af (_, _, inicial, _, finales) as a) =
      let rec aux = function
           (Conjunto [], _) ->
              false
         | (actuales, []) ->
              not (es_vacio (interseccion actuales finales))
         | (actuales, simbolo :: t) ->
              aux (avanza simbolo actuales a, t)
      in
         aux (Conjunto [inicial], cadena)
      ;;

  (* Ejemplo:
      let a4 = af_of_string "0 1 2 3 4; a b c; 0; 3; 0 1 a; 1 2 b; 2 3 a; 0 2 a; 0 4 b;";;
      let cad1 = Ergo.cadena_of_string "a b a";;
      escaner_afn cad1 a4;; *)
  
  let string_of_stado s = match s with Estado st -> st;;
  let string_of_symbol s = match s with Terminal st -> st | No_terminal s -> s;;

  let get_next_state_afd state symbol automata =
    let arcs = match automata with
      | Af (_,_,_,t,_) -> t
    in
    let rec aux = function
      | Conjunto [] -> raise Not_found
      | Conjunto (h::t) ->
        let i = match h with
          | Arco_af (inn,_,_) -> inn
        in
        let s = match h with
          | Arco_af (_,_,s) -> s
        in
        if i = state && s = symbol then
          match h with
            | Arco_af (_,enn,_) -> enn
        else
          aux (Conjunto t)
    in
    aux arcs
  ;;  

  let escaner_afd cadena (Af (_, _, inicial, _, finales) as a) =
    let rec aux state = function
      | [] -> not (es_vacio (interseccion (Conjunto [state]) finales))
      | h::t -> 
        try 
         let next_state = get_next_state_afd state h a in 
           aux next_state t
        with Failure s  -> false
    in aux inicial cadena
  ;;
  
  (* Ejemplo:
      let a5 = af_of_string "0 1 2 3 4; a b c; 0; 3; 0 1 a; 1 2 b; 2 3 a; 0 4 b;";;
      let cad2 = cadena_of_string "a b a";;
      escaner_afn cad2 a5;; *)