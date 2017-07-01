theory Simplificacion
imports Main
begin

section {* El método de simplificación *}

section {* Seguimiento de la simplificación  *}

lemma "rev [x] = [x]"
using [[simp_trace]] 
apply simp
done

text {* El resultado de la traza es
     proof (prove)
     goal:
     No subgoals! 
     [1]SIMPLIFIER INVOKED ON THE FOLLOWING TERM:
     rev [x] = [x] 
     [1]Applying instance of rewrite rule "??.unknown":
     rev (?x1 # ?xs1) \<equiv> rev ?xs1 @ [?x1] 
     [1]Rewriting:
     rev [x] \<equiv> rev [] @ [x] 
     [1]Applying instance of rewrite rule "??.unknown":
     rev [] \<equiv> [] 
     [1]Rewriting:
     rev [] \<equiv> [] 
     [1]Applying instance of rewrite rule "List.append.append_Nil":
     [] @ ?y \<equiv> ?y 
     [1]Rewriting:
     [] @ [x] \<equiv> [x] 
     [1]Applying instance of rewrite rule "HOL.simp_thms_6":
     ?x1 = ?x1 \<equiv> True 
     [1]Rewriting:
     [x] = [x] \<equiv> True
     
  El significado de la traza es
       (rev [x]      = [x])
     = (rev [] @ [x] = [x])     [por "rev (x1 # xs1) = rev xs1 @ [x1]"] 
     = ([]     @ [x] = [x])     [por "rev [] = []"]
     = ([x]          = [x])     [por List.append.append_Nil]
     = True                     [por HOL.simp_thms_6]
*}

text{* Ejemplo de simplificación no condicional *}
lemma "(ys @ [] = []) = 
       (ys = [])"
apply simp
done

text{* Ejemplo de simplificación usando supuestos *}
lemma "\<lbrakk> xs @ zs = ys @ xs
       ; [] @ xs = [] @ [] \<rbrakk> 
       \<Longrightarrow> ys = zs"
apply simp
done

lemma 
  "\<lbrakk>  0 + n           = n
   ; (Suc m) + n     = Suc (m + n)
   ; (Suc m \<le> Suc n) = (m \<le> n)
   ; (0 \<le> m)         = True \<rbrakk>
   \<Longrightarrow> 0 + Suc 0 \<le> (Suc 0) + x"
apply simp
done

text {* Ejemplo de simplificación con reglas auxiliares *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply (simp add: algebra_simps)
done

text {* Las reglas de algebra_simps son 
  (a + b) + c = a + (b + c)
  a + b = b + a
  b + (a + c) = a + (b + c)
  (a * b) * c = a * (b * c)
  a * b = b * a
  b * (a * c) = a * (b * c)
  a - (b - c) = a - (b + c)
  a + (b - c) = a + b - c
  (a - b = c) = (a = c + b)
  (a = c - b) = (a + b = c)
  a - (b - c) = (a + c) - b
  (a - b) + c = (a + c) - b
  (a - b < c) = (a < c + b)
  (a < c - b) = (a + b < c)
  (a - b \<le> c) = (a \<le> c + b)
  (a \<le> c - b) = (a + b \<le> c)
  (a + b) * c = a * c + b * c
  a * (b + c) = a * b + a * c
  a * (b - c) = a * b - a * c
  (b - c) * a = b * a - c * a
  a * (b - c) = a * b - a * c
  (a - b) * c = a * c - b * c
*}
thm algebra_simps

text {* Declaración de reglas como de simplificación *}
declare algebra_simps [simp]

text {* Ejemplo de simplificación con declaradas como simplificadores *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply simp
done

section {* Reescritura condicional *}

lemma aux1: "P 0"
sorry

lemma aux2: "P x \<Longrightarrow> f x = g x"
sorry

lemma "f 0 \<Longrightarrow> g 0"
apply (simp add: aux1 aux2)
done

lemma "f 1 \<Longrightarrow> g 1"
apply (simp add: aux1 aux2)
oops

section {* Reescritura con definiciones *}

text {* Ejemplo de definición: (cuadrado x) es el cuadrado de x. Por
  ejemplo, 
     cuadrado (Suc (Suc 0)) = Suc (Suc (Suc (Suc 0)))
*}
definition cuadrado :: "nat \<Rightarrow> nat" 
where
  "cuadrado n = n*n"

value "cuadrado (Suc (Suc 0))"

text {* Ejemplo de lema con reescritura usando definición: *}
lemma "cuadrado (Suc (Suc 0)) = Suc (Suc (Suc (Suc 0)))" 
apply (simp add: cuadrado_def)
done

text {* Ejemplo de lema con reescritura usando definición: *}
lemma "cuadrado(n*n) = cuadrado(n)*cuadrado(n)"
apply (simp add: cuadrado_def) 
done

subsection{* Distinción de casos *}

text {* Ejemplos de distinción automática de casos con if *}
lemma "P (if A then s else t)
       = ((A \<longrightarrow> P(s)) \<and> (\<not>A \<longrightarrow> P(t)))"
apply simp
done

lemma "(if A then B else False)
       = (A \<and> B)"
apply simp
done

lemma "(if A then B else C)
       = ((A \<longrightarrow> B) \<and> (\<not>A \<longrightarrow> C))"
apply simp
done

text {* Ejemplos de distinción no automática de casos con case *}

lemma "P (case e of 0 \<Rightarrow> a | Suc n \<Rightarrow> b)
       = ((e = 0 \<longrightarrow> P(a)) \<and> (\<forall> n. e = Suc n \<longrightarrow> P(b)))"
apply (simp split: nat.split)
done

lemma "P (case xs of [] \<Rightarrow> a | (y#ys) \<Rightarrow> b) 
       = ((xs = [] \<longrightarrow> P a ) \<and> ((\<exists>y ys. xs = y # ys) \<longrightarrow> P b))"
apply (simp split: list.split)
done

lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
apply (simp split: list.split)
done

lemma "P (case t of (x,y) \<Rightarrow> f x y)
       = (\<forall> x y. t = (x,y) \<longrightarrow> P (f x y))"
apply (simp split: prod.split)
done

text {* Ejemplos de distinción no automática de casos con let *}

lemma "P (let (x,y) = t in f x y)
       = (\<forall> x y. t = (x,y) \<longrightarrow> P (f x y))"
apply (simp split: prod.split)
done

section {* Simplificación en aritmética lineal *}

text {* Ejemplo de simplificación con las reglas de la aritmética
  lineal. *} 
lemma "\<lbrakk> (x::nat) \<le> y+z
       ; z+x < y \<rbrakk> 
       \<Longrightarrow> x < y"
apply simp
done

end
