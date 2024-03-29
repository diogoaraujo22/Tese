-- Modelo blockchain para representar transações bitcoin. Os primeiros 2 blocos são apenas de inicialização e não seguem 
-- certas regras que devem ser cumpridas pelo protocolo.  


-----------------------------
-- Blockchain Structure
-----------------------------


sig Block{
	tx       : one Tx,
	Next   : lone Block	
}

one sig BlockI extends Block{} 

sig Transaction{
	txid       : one Word,  -- hash de transação
	fee       : one Int,      -- transaction fee paid to miner
	input    : set Input,    -- input set
	output  : set Output  -- output set
}

sig Tx{
	merkleRoot : one Word, --merkle root
  	transaction : set Transaction
}

sig Word{}


sig Input{
	txid       : one Word, -- transaction id where utxo was created
	value   : one Int,      -- value in Satoshis aka SATS
	sender : one BAddr -- bitcoin address from the person who owns the bitcoins
					-- one transaction can have multiple senders  
}

sig Output{
	value : one Int,       -- value in Satoshis aka SATS
	to       : one BAddr, -- bitcoin address to the receiver
	
}

sig BAddr{}


--------------------
-- Functions
--------------------

-- função que retorna as hashes não utilizadas em merkleroots e txid
fun nonUsedHashesMrTxid : set Word
	{Word - Tx.merkleRoot-txFromBlocks[Block].txid - inputsFromBlocks[afterSndBlock].txid}

-- função que retorna os inputs associados a transações
fun confirmedInputs : set Input
	{Block.tx.transaction.input} 

-- função que retorna os outputs associados a transações
fun confirmedOutputs : set Output
	{Block.tx.transaction.output} 

-- função que retorna os inputs orfãos
fun orphanInputs : set Input
	{Input - confirmedInputs} 

-- função que retorna os outputs orfãos
fun orphanOutputs : set Output
	{Output -  confirmedOutputs}


-- função que retorna as Transações orfãs
fun orphanTransactions : set Transaction
	{Transaction - Block.tx.transaction}

-- função que retorna todos os blocos sucessores de um bloco b
fun afterBlock[b:Block] : set Block
	{{x:Block | x in b.^(Next)}} 


-- função que retorna todos os blocos sucessores ao 2º bloco
fun afterSndBlock : set Block
	{{x:Block | x in (BlockI.Next).^(Next)}} 


-- função que retorna todos os inputs sucessores ao 2º bloco
fun inputAfterSndBlock : set Input
	{{i:confirmedInputs | i in afterSndBlock.tx.transaction.input}} 

-- função que retorna todos os blocos precedentes de um bloco b
fun untilBlock[b:Block] : set Block
	{{x:Block | x in b.^(~Next)}} 


-- função que retorna o bloco onde um input se situa
fun blockFromInput[i:Input] : one Block
	{{b:Block | i in b.tx.transaction.input}}


-- função que retorna as transações de um conjunto de blocos 
fun txFromBlocks[bs : set Block] : set Transaction
	{{t:Transaction | t in bs.tx.transaction}}


-- função que retorna as transações de um conjunto de blocos 
fun inputsFromBlocks[bs : set Block] : set Input
	{{i:Input | i in bs.tx.transaction.input}}


-- função que retorna as transações precedentes ao bloco onde se situa um input
fun precTxFromInput[i : one Input] : set Transaction
	{txFromBlocks[untilBlock[blockFromInput[i]]]}


-- função que retorna a transação onde um input foi criado
fun originTx[i : one Input] : one Transaction
	{{t : Transaction | i.txid = t.txid}}

-- função auxliar de associatedOutput
fun associatedOutputAux[i : one Input, t : one Transaction] : one Output
	{{o:Output | o in t.output and i.value = o.value and i.sender = o.to}}

-- função que retorna o output associado a um input 
fun associatedOutput[i : one Input] : one Output
	{associatedOutputAux[i, originTx[i]]}


-- função que retorna os utxos de um endereço bitcoin
fun utxos[a : one BAddr] : set Output
	{{o : Output | o in (to.a - associatedOutput[sender.a])}}


-- função que retorna os endereços bitcoin utilizados a partir do 2º bloco
fun usedAddresses : set BAddr
	{afterSndBlock.tx.transaction.input.sender}

-- função que retorna os valores bitcoin utilizados a partir do 2º bloco
fun usedValues : set Int
	{afterSndBlock.tx.transaction.input.value}

-- função que retorna a soma dos valores dos outputs de uma transação
fun sumOutputValues[t: Transaction]: Int 
	{sum o: t.output | o.value}

-- função que retorna a soma dos valores dos inputs de uma transação
fun sumInputValues[t: Transaction]: Int 
	{sum o: t.input | o.value}

-- função que retorna a soma dos valores dos outputs + fee de uma transação
fun sumOutputsValuesFee[t:Transaction] : Int
	{plus[sumOutputValues[t],t.fee]}


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
	{all iv:Input.value, ov:Output.value, f: Transaction.fee | iv>0 and ov>0 and f>0}


-- 6. a merkleroot não coincide com a hash de uma transacao
pred propDisjMerklerootTxid
	{no Tx.merkleRoot & Transaction.txid}


-- 7. transações distintas não têm a mesma hash (txid injectivo). 
pred propNotSameTxid
	{(Transaction<:txid).~(Transaction<:txid) in iden}

-- 8. a merkleroot não coincide com a txid de um input
pred propDisjMerklerootTxidInput
	{no Tx.merkleRoot & Input.txid}


-- 9. tx injetivo (Não ha dois blocos com a mesma lista de transações/merkleroot)
pred propNotSameTx
	{tx.~tx in iden}

-- 10. merkleroot injetivo (Não ha dois blocos com a mesma merkleroot)
pred propNotSameMerkleRoot
	{merkleRoot.~merkleRoot in iden}


-- 11. a txid de um input não pode coicidir com a hash da transação onde se situa
pred propOrderedTxid
	{all tx : Tx | no tx.transaction.input.txid & tx.transaction.txid}


-- 12.  2 blocos distintos não podem ter a mesma transação 
pred propNotSameTransaction
	{transaction.~transaction in iden}


-- 13. um input de uma transação situada no bloco n foi criado por uma transação situada num bloco precedente ao bloco n
pred propSequenceInput
	{all i:inputAfterSndBlock | one t: precTxFromInput[i] | i.txid = t.txid}


-- 14. input injectivo 
pred propNotSameInput
	{input.~input in iden}


-- 15. as txid dos inputs dos 2 primeiros blocos não coincidem com outras hashes (não referem transações anteriores)
pred propInputsFirst2Blocks 
	{inputsFromBlocks[Block-afterSndBlock].txid in nonUsedHashesMrTxid}


-- 16. um input de uma transação refere um output da transação onde o input foi criado
pred propReferenceInputOutput
	{all i:inputAfterSndBlock | one o: originTx[i].output | i.value = o.value and i.sender = o.to}


-- 17. input values = output values + fee
pred propBalanceValues
	{all t:Transaction | sumInputValues[t] = sumOutputsValuesFee[t]}


--- Block Next Predicates-- 
-- 18. o next de um bloco nao pode ser ele mesmo. 
pred propNoConfusionNext 
	{no Next & iden}


-- 19. blocos distintos não tenham o mesmo Next
pred propNoBlocksSameNext
	{all b:Block | lone Next.b}


-- 20. não há ciclos. all b : Block | b not in b.^Next 
pred propNoCycleChain
	{no ^Next & iden}


-- 21.  BlockI é o bloco inicial. all bi : BlockI | no b : Block | b.Next = bi
pred propInitialBlockI
	{no Next.BlockI}

-- 22. todos os blocos já consolidados são alcançaveis a partir do BlockI
pred propReachableFromBlockI
	{all b : Block-BlockI | b in BlockI.^Next}
--------------------------


----- Better understading predicates 
-- 23. 
pred propXInputs
	{all t:Transaction | #t.input = 2}

-- 24.
pred propXOutputs
	{all t:Transaction | #t.output = 2}

-- 25. output injectivo.
pred propNotSameOutput
	{output.~output in iden}

-- 26. no orpahn transactions 
pred propNoOrpahnTransactions 
	{no orphanTransactions}

-- 27. mais de X endereços usados 
pred propMoreThanXUsedAddresses
	{#usedAddresses = 4}

-- 28. mais de X valores usados 
pred propMoreThanXUsedValues
	{#usedValues = 4}




fact Facts{
	-- 1.
	propAtLeastOneInOneOut

	-- 2.
	propNoOrphanInputs
 
	-- 3. 
	propNoOrphanOutputs
	
	-- 4.
	propAtLeastOneTransaction

	-- 5.
	propPositiveValues

	-- 6.
	propDisjMerklerootTxid

	-- 7.
	propNotSameTxid

	-- 8.
	propDisjMerklerootTxidInput

	-- 9.
	propNotSameTx

	-- 10.
	propNotSameMerkleRoot

	-- 11.
	propOrderedTxid

	-- 12.
	propNotSameTransaction

	-- 13.
	propSequenceInput

	-- 14.
	propNotSameInput
	
	-- 15.
	propInputsFirst2Blocks

	-- 16.
	propReferenceInputOutput

	-- 17.
	propBalanceValues
	
	---------- Block Next Predicates----
	-- 18.
	propNoConfusionNext

	-- 19.
	propNoBlocksSameNext
	
	-- 20. 
	propNoCycleChain

	-- 21.
	propInitialBlockI

	-- 22.
	propReachableFromBlockI
	-----------------------------



	----- Better understading predicates ---
	-- 23. 
	propXInputs

	-- 24.
	propXOutputs

	-- 25. 
	propNotSameOutput

	-- 26.
	propNoOrpahnTransactions
	
	-- 27.
	propMoreThanXUsedAddresses
	
	-- 28.
	propMoreThanXUsedValues
	-----------------------------

}



-----------
-- Run
-----------

run{

} for 30 but exactly 5 Block

