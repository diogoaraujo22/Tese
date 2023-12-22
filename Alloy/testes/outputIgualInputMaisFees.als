open util/integer

sig Transaction{
	fee : one Int,
	input :  set Input,
	output : set Output
}

sig Input{
	value : one Int, -- value in Satoshis aka SATS
}

sig Output{
	value : one Int, -- value in Satoshis aka SATS
}


-- função que retorna os inputs orfãos
fun orphanInputs : set Input
	{Input - Transaction.input} 

-- função que retorna os outputs orfãos
fun orphanOutputs : set Output
	{Output - Transaction.output}




-- função que retorna os outputs orfãos
fun soma[o : set Output] : Int 
	{sum o.value}


fun addd[a, b: Int]: Int {
  {i: Int | i = int a + int b}
}


-- Retorna todos os pares Output->Int de uma transação
fun getOutputPairs[t: Transaction]: set Output->Int 
	{{o: t.output, v: o.value}}

fun getSecondColumn[outputPairs: set Output->Int]: set Int {
  	{disj value: Int | all o: Output | (o->value) in outputPairs}
}


fun exemplo[outputPairs: set Output->Int]: one Int {
  	{{sum Output.outputPairs}}
}

-- função 
--fun sumOutputs[t:Transaction] : Int
--	{sum getOutputPairs[t]}










/*
-- função 
fun sumOutputs[t:Transaction] : Int
	{sum t.output.value}

-- função 
fun sumInputs[t:Transaction] : Int
	{sum t.input.value}

-- função 
fun sumOutputsFee[t:Transaction] : Int
	{plus[sumOutputs[t],t.fee]}

pred prop
	{all t:Transaction | int sumInputs[t] = nt sumOutputsFee[t]}
*/


fun sumOutputValues[t: Transaction]: Int 
	{sum o: t.output | o.value}


fun sumInputValues[t: Transaction]: Int 
	{sum o: t.input | o.value}


fun sumOutputsValuesFee[t:Transaction] : Int
	{plus[sumOutputValues[t],t.fee]}



pred prop
	{all t:Transaction | sumInputValues[t] = sumOutputsValuesFee[t]}


run{
	---
	#Transaction = 2
	all t : Transaction | #t.input = 3
	all t : Transaction | #t.output = 1
	---
	all v:Input.value | v>0 
	all v:Output.value | v>0
	all v:Transaction.fee | v>0 

	--
	prop
	---
	no orphanInputs
	no orphanOutputs
	fee.~fee in iden

	//prop
	---
--	all t : Transaction | sumOutputs[t] = 5
	---
	--(Output<:value).~(Output<:value) in iden

	--all t : Transaction | t.fee + t.input.value = t.output
--	all t: Transaction | t.fee + sum i: t.input | i.value = sum o: t.output | o.value
 	--#Transaction.fee = 1

} for 30
