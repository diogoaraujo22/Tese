-- Propositiones ad Acuendos Juvenes
-- XVIII. PROPOSITIO DE HOMINE ET CAPRA ET LVPO.
-- Alloy book: A.3.5: Ovelha, Couve, Lobo
-- http://www.archimedes-lab.org/atelier.html?http://www.archimedes-lab.org/earlymathpuzzlers/alcuin_propositiones.html

open util/ordering[Tempo]

abstract sig Ser {
	Come : set Ser
}

one sig Homem, Couve, Ovelha, Lobo extends Ser {}

abstract sig Margem { 
    atravessa: Margem
}

one sig Esquerda, Direita  extends Margem {}

sig Tempo { onde : Ser -> one Margem }

fact {
   Come      = Lobo -> Ovelha + Ovelha -> Couve
   atravessa = Esquerda -> Direita  + Direita -> Esquerda
}

fun MesmaMargem[t:Tempo] : Ser -> Ser
      { (t.onde).~(t.onde) } -- ker s.onde

fun move[w: Ser -> one Margem, 
         q: set Ser]: Ser -> one Margem 
     { w ++ (q <: w).atravessa }
 
pred transita[t,t':Tempo, quem: set Ser]
      { t'.onde = move[t.onde,quem] }

pred esfomeados[s: Tempo]{  
       (s.MesmaMargem & Come).(s.onde) 
             in (Ser->Homem).(s.onde)
}

pred viagem[t,t' : Tempo] {
    some c: (t.MesmaMargem).Homem |
             transita[t,t',Homem + c]
}

fact {
  all s : Tempo | esfomeados[s]
  first.onde = Ser->Esquerda
  last.onde = Ser->Direita 
  all t : Tempo, t' : t.next | viagem[t,t']
}

-- run { last.onde = Ser->Direita } for 3 but exactly 8 Tempo

 run { } for 3 but exactly 8 Tempo
