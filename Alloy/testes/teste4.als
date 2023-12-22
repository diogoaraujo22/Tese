abstract sig Bool{}

one sig True, False extends Bool{} 

sig Block{
	tx : one Tx
}

sig Transaction{
	txid : one Word, --hash de transação
	fee : one Int,
	input :  set Input,
	output : set Output,
	sendsby: one Sender
}


sig Tx{
	merkleRoot : one Word, --merkle root
  	transaction : set Transaction
}

sig Word{}
sig PubKey{}
sig Signature{
	validationFunction : one Bool
}

sig Sender{
	privKey : one PrivKey,
}

sig PrivKey{
	generates : one PubKey,
	signs : one Signature
}

sig Input{
	txid : one Word, -- transaction id where utxo was created
	value : one Int, -- value in Satoshis aka SATS
	from : one BAddr -- bitcoin address from the sender
}

sig Output{
	value : one Int, -- value in Satoshis aka SATS
	to : one BAddr, -- bitcoin address to the receiver
	
}

sig BAddr{}

--------------------
-- Functions
--------------------

-- função que retorna os inputs orfãos
fun orphanInputs : set Input
	{Input - Transaction.input} 

-- função que retorna os outputs orfãos
fun orphanOutputs : set Output
	{Output - Transaction.output}

-- função que retorna as private keys orfãs
fun orphanPrivKeys: set PrivKey
	{PrivKey - Transaction.sendsby.privKey}


-- função que retorna os senders orfãos
fun orphanSenders: set Sender
	{Sender - Transaction.sendsby}

-- função que retorna as transações válidas
fun validTransactions: set Transaction
	{{t:Transaction | t.sendsby.privKey.signs.validationFunction = True}} 


-- função que retorna as transações inválidas
fun rejectedTransactions: set Transaction
	{Transaction - validTransactions}

--------------------
-- Predicates
--------------------

-- 1. Todas as transações tem pelo menos 1 input e 1 output
pred propAtLeastOneInOneOut
	{all t : Transaction | some t.input and some t.output}


-- 2. Não ha inputs que não estejam associados a transações
pred propNoOrphanInputs
	{no orphanInputs}

-- 3. Não ha outputs que não estejam associados a transações
pred propNoOrphanOutputs
	{no orphanOutputs}

-- 4. Todos os Tx têm pelo menos 1 transação
pred propAtLeastOneTransaction
	{all t:Tx | some t.transaction}

-- 5. Os valores transferidos têm de ser positivos
pred propPositiveValues
	{all iv:Input.value, ov:Output.value | iv>0 and ov>0}


-- 6. Todas as Transações de um bloco têm de passar na função de validação
pred propOnlyValidTransactions
	{all b:Block | b.tx.transaction in validTransactions}


-- 7. a merkleroot não coincide com a hash de uma transacao
pred propDisjMerklerootTxid
	{no Tx.merkleRoot & Transaction.txid}


-- 8. nao existem private keys orfãs
pred propNoOrphanPrivKeys
	{no orphanPrivKeys}


-- 9. transações distintas não têm a mesma hash (txid injectivo). 
pred propNotSameTxid
	{(Transaction<:txid).~(Transaction<:txid) in iden}

-- 10. a merkleroot não coincide com a txid de um input
pred propDisjMerklerootTxidInput
	{no Tx.merkleRoot & Input.txid}

-- 11. nao existem Senders orfãos
pred propNoOrphanSenders
	{no orphanSenders}


-- 12. privKey injetivo (Não ha dois senders com a mesma private key)
pred propNotSamePrivKey
	{privKey.~privKey in iden}


-- 13. generates injetivo (Não ha duas private keys com a mesma public key)
pred propNotSamePubKey
	{generates.~generates in iden}

-- 14. tx injetivo (Não ha dois blocos com a mesma lista de transações/merkleroot)
pred propNotSameTx
	{tx.~tx in iden}








-------- predicados para melhor compreesão
-- 1 transação não tem mais que 3 inputs (só para simplificar)
pred propNoMoreThan3Inputs
	{all t:Transaction | #t.input < 3}

-- 1 transação não tem mais que 3 output (só para simplificar)
pred propNoMoreThan3Outputs
	{all t:Transaction | #t.output < 3}

-- n blocos
pred propOneBlock
	{#Block = 4}

-- output injectivo 
pred propNotSameOutput
	{output.~output in iden}

-- input injectivo 
pred propNotSameInput
	{input.~input in iden}





fact Facts{
propAtLeastOneInOneOut
propNoOrphanInputs
propNoOrphanOutputs
propAtLeastOneTransaction
propPositiveValues
propOnlyValidTransactions
propDisjMerklerootTxid
propNoOrphanPrivKeys
propNotSameTxid
propDisjMerklerootTxidInput
propNoOrphanSenders
propNotSamePrivKey
propNotSamePubKey
propNotSameTx



-- melhor compreensao
propNoMoreThan3Inputs
propNoMoreThan3Outputs
propOneBlock
propNotSameOutput
propNotSameInput

}






-- CREATE TRANSATION


run{
	#rejectedTransactions = 1
	#Transaction = 4
	#Block = #Tx
 	--#Transaction.fee = 1

} for 6
