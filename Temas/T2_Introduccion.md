theory T2_Introduccion
imports Main
begin

section {* Comentarios *}

(* Esto es un comentario para Isabelle y para LaTeX *)

text {* Esto es un comentario para Isabelle pero no para LaTeX *}

section {* Inferencia de tipo *}

text {* (term t) muestra el tipo del término t. *}

term "True"          (* da "True" :: "bool" *)
term "False"         (* da "False" :: "bool" *)
term "true"          (* da "true" :: "'a" *)
term "True & False"  (* da "True ∧ False" :: "bool" *)
term "True & false"  (* da "True ∧ false" :: "bool" *)

text {*
  + Para ver el tipo de un término, poner el curso sobre él y pulsar
    ~Ctrl~.
  + Para ver la definición de un término, poner el curso sobre él, 
    pulsar ~Ctrl~ y pulsar el botón izquierdo del ratón.  
*}

section {* Evaluación de términos *}

text {* (value t) muestra el valor del término t. *}

value "True & False" (* da "False" :: "bool" *)
value "True & P"     (* da "P" :: "bool" *)

section {* Ejemplos de sobrecarga *}

text {* Los números y las operaciones aritméticas están sobrecargados *}

term "n + n = 0"
term "(n::nat) + n = 0"

(*Try this:

term "True + False"

Terms must be type correct!*)

text{* Type inference: *}

term "f (g x) y"
term "h (%x. f(g x))"
term "%x. x + x"

end
