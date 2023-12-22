

// Assinatura para representar um conjunto de inteiros
abstract sig Conjunto {
  elementos: set Int
}

sig C1 extends Conjunto{}

// Função para calcular a soma de um conjunto de inteiros
fun somar[conjunto: Conjunto]: Int {
  sum e: conjunto.elementos | e
}


fact {
   elementos      = C1 -> 2 + C1 -> 2 + C1 -> 3 + C1 -> 2 + C1 -> 1 + C1 -> 6
}

fun mysum[c: set Int] : Int{
	let a = c.first



}

run{
	--#Conjunto.elementos = 5
} for 6
