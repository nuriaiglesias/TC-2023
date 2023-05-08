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

  (* Si tiene epsilon *)
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

  (* Un estado una entrada, varias transiciones *)
  let es_afn (Af (_,_,_,arcs,_)) =
    let rec loop transicion_v boolean = function
      Conjunto ((Arco_af(s1,_,terminal))::tl) ->
          (* Epsilon se ignora *)
        if terminal = (Terminal "") then
          loop transicion_v boolean (Conjunto(tl))
          (* Transicion visitada *)
        else if pertenece (s1,terminal) transicion_v then
          loop (agregar (s1,terminal) transicion_v) true (Conjunto(tl))
          (* Agregar a conj visitado *)
        else
          loop (agregar (s1,terminal) transicion_v) boolean (Conjunto(tl))
      | Conjunto _ -> boolean
    in loop (Conjunto []) false arcs
  ;;

  (* es_afn eq2: true
     es_afn eq3: false *)

  (* Contador del par estado-simbolo en transiciones *)
  let repetido (estado,simbolo) transiciones =
    let rec contador cont = function
        (* Comprobación del valor cont *)
      | Conjunto [] -> cont = 1
        (* Comprobación estado-simb +1 transicion *)
      | Conjunto (Arco_af (e,_, s)::tl) when estado=e && simbolo=s && s<>(Terminal "") ->
          (* False si ya ha aparecido antes *)
          (cont > 1) || contador (cont+1) (Conjunto tl)
        (* Transicion actual no es estado, simb seguimos buscando *)
      | Conjunto (Arco_af _::tl) -> 
          contador cont (Conjunto tl)
    in contador 0 transiciones;;

    (* Estados sin repetir y sin epsilon *)
  let es_afd (Af (estados,simbolos,_,transiciones,_)) =
    let rec recorrer_estados = function
      | Conjunto [] -> true
      | Conjunto ((Estado est)::estado_tl) ->
        let rec verificar_simb = function
          | Conjunto [] -> true
            (* Comprobacion 1 estado-simb *)
          | Conjunto ((Terminal s)::simbolo_tl) -> 
              if (repetido (Estado est, Terminal s) transiciones) then
                verificar_simb (Conjunto simbolo_tl)
              else
                false
            (* Comprobación no terminales *)
          | Conjunto ((No_terminal s)::_) -> 
              false
          (* Comprobamos simb y simb de sig estados *)
        in verificar_simb simbolos && recorrer_estados (Conjunto estado_tl)
    in recorrer_estados estados;;

    (* es_afn eq2: false
      es_afn eq3: true *)

  (* EJERCICIO 2 *)

  (* Transicion entre dos estados *)
  let rec transition estado value (Conjunto arcoAf) = match arcoAf with 
      [] -> estado
    | Arco_af(estado_partida,estado_llegada,simb)::t -> 
      if estado_partida = estado && simb = value then 
            (* Transicion epsilon *)
            if (simb <> Terminal "") && (estado_partida = estado_llegada) then 
              transition estado value (Conjunto t)
            (* Transicion encontrada *)
            else estado_llegada
      else transition estado value (Conjunto t)
;;

(* Comprobación de 2 autómatas aceptación mismo lenguaje, aceptan o rechazan las mismas cadenas *)
let equivalentes (Af(_,simbolos1, inicial1, arcos1, finales1)) (Af(_, simbolos2, inicial2,arcos2, finales2)) =
  (* Creación alfabeto + epsilon *)
  let alfabeto = agregar (Terminal "") (union simbolos1 simbolos2) in 
  (* Recorremos todos los estados posibles *)
  let rec loop (Conjunto a_visitar) visitados =  match a_visitar with
      [] -> true
    | (estadoAct1, estadoAct2)::t ->  
        (* Si ya visitó el estado actual, se omite *)
      if pertenece (estadoAct1, estadoAct2) visitados then loop (Conjunto t) visitados
          (* Si uno de los estados es final y el otro no, no son eq *)
        else if (pertenece estadoAct1 finales1 && not (pertenece estadoAct2 finales2)) 
              || (not (pertenece estadoAct1 finales1) && pertenece estadoAct2 finales2) then 
                false
        else
              (* Los añado a visitados *)
            let vistos1 = agregar (estadoAct1, estadoAct2) visitados in 
              (* Visitamos simb *)
            let rec loopAux (Conjunto alf) vistos= match alf with
              [] -> true
                (* Generamos los nuevos estados, alcanzados por el estado actual *)
              | a::l -> let nuevoEtd1 = transition estadoAct1 a arcos1 in 
                    let nuevoEtd2 =  transition estadoAct2 a arcos2 in
                    if (not (pertenece (nuevoEtd1, nuevoEtd2) vistos)) then
                        (* Nuevos estados generados igual a estado actual, se ignora *)
                      if (a<>(Terminal "") && (nuevoEtd1 = estadoAct1 || nuevoEtd2 = estadoAct2)) then 
                        loopAux (Conjunto l)  vistos 
                        (* Si no, lo agregamos a visitar *)
                      else 
                        loop (agregar (nuevoEtd1, nuevoEtd2) (Conjunto a_visitar)) vistos 
                    else loopAux (Conjunto l)  vistos 
            in loopAux alfabeto vistos1
  in loop (Conjunto [(inicial1,inicial2)])  (Conjunto []) 
;;


  (* EJERCICIO 3 *)


let escaner_af cadena (Af (_, _, inicial, _, finales) as a) =
  let rec aux = function
       (Conjunto [], _) ->
          false
     | (actuales, []) ->
          not (es_vacio (interseccion actuales finales))
     | (actuales, simbolo :: t) ->
          aux ((epsilon_cierre (avanza simbolo actuales a) a), t)
  in
     aux ((epsilon_cierre (Conjunto [inicial]) a), cadena)
  ;;

  (* Cadena de símb aceptada por AFN *)
  let escaner_afn cadena (Auto.Af (_, _, inicial, _, finales) as a) =
      let rec aux = function
          (* No hay más transiciones a realizar *)
           (Conjunto [], _) ->
              false
          (* Comprueba que estados actuales sean finales, devuelve true *)
         | (actuales, []) ->
              not (es_vacio (interseccion actuales finales))
         | (actuales, simbolo :: t) ->
              aux (avanza simbolo actuales a, t)
      in
         aux (Conjunto [inicial], cadena)
      ;;

  (* Implementación más directa, mejor para AFN, peor para otros *)
  (* Ejemplo:
      let a4 = af_of_string "0 1 2 3 4; a b c; 0; 3; 0 1 a; 1 2 b; 2 3 a; 0 2 a; 0 4 b;";;
      let cad1 = cadena_of_string "a b a";;
      escaner_afn cad1 a4;; *)
  
  let rec escaner_afd cadena (Af (_, _, inicial, _, finales) as a) =
    let rec aux state = function
        (* Si está vacía, comprueba que sea estado final *)
      | [] -> not (es_vacio (interseccion (Conjunto [state]) finales))
      | h::t ->
        let next_state = transition state h (match a with Af (_,_,_,t,_) -> t) in
        aux next_state t
    in aux inicial cadena
  ;;
  
  (* Ejemplo:
      let a5 = af_of_string "0 1 2 3 4; a b c; 0; 3; 0 1 a; 1 2 b; 2 3 a; 0 4 b;";;
      let cad2 = cadena_of_string "a b a";;
      escaner_afd cad2 a5;; *)