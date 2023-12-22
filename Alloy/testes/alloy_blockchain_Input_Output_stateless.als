-- Modelo blockchain para representar transações bitcoin. Os primeiros 2 blocos são apenas de inicialização e não seguem 
-- certas regras que devem ser cumpridas pelo protocolo.  


sig Block{
	tx : one Tx,
	Next   : lone Block	
}

one sig BlockI extends Block{} 

sig Transaction{
	txid : one Word,      -- hash de transação
	fee : one Int,          -- transaction fee paid to miner
	input :  set Input,    -- input set (utxo's)
	output : set Output -- output set
}

sig Tx{
	merkleRoot : one Word, --merkle root
  	transaction : set Transaction
}

sig Word{}


sig Input{
	txid : one Word,       -- transaction id where utxo was created
	value : one Int,        -- value in Satoshis aka SATS
	sender : one BAddr -- bitcoin address from the person who owns the bitcoins
					 -- one transaction can have multiple senders  
}

sig Output{
	value : one Int, -- value in Satoshis aka SATS
	to : one BAddr, -- bitcoin address to the receiver
	
}

sig BAddr{}




--------------------
-- Functions
--------------------

-- função que retorna as hashes não utilizadas em merkleroots e txid
fun nonUsedHashesMrTxid : set Word
	{Word - Tx.merkleRoot-txFromBlocks[effectiveBlocks].txid - inputsFromBlocks[afterSndBlock].txid}

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


-- função que retorna os blocos já consolidados
fun effectiveBlocks : set Block 
	{Next.Block + Block.Next} 


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


-- 11. todas as txid dos inputs referem hashes de outras transações já consolidadas
--pred propReferenceTxid
--	{Input.txid in Transaction.txid}


-- 12. a txid de um input não pode coicidir com a hash da transação onde se situa
pred propOrderedTxid
	{all tx : Tx | no tx.transaction.input.txid & tx.transaction.txid}

----------------------- Next things ----------------
-- 13. o next de um bloco nao pode ser ele mesmo. all b : Block | b->b not in Next
pred propNoConfusionNext 
	{no Next & iden}


-- 14. blocos distintos não tenham o mesmo Next
pred propNoBlocksSameNext
	{all b:effectiveBlocks | lone Next.b}


-- 15. não há ciclos. all b : Block | b not in b.^Next 
pred propNoCycleChain
	{no ^Next & iden}


-- 16.  BlockI é o bloco inicial. all bi : BlockI | no b : Block | b.Next = bi
pred propInitialBlockI
	{no Next.BlockI}

-- 17. todos os blocos já consolidados são alcançaveis a partir do BlockI. always all bi : BlockI, b : Block - bi | b in effectiveBlocks implies b in bi.^Next
pred propReachableFromBlockI
	{all b : effectiveBlocks-BlockI | b in BlockI.^Next}
----------------------- end Next things ----------------


-- 18.  2 blocos distintos não podem ter a mesma transação 
pred propNotSameTransaction
	{transaction.~transaction in iden}


-- 19. um input de uma transação situada no bloco n foi criado por uma transação situada num bloco precedente ao bloco n
pred propSequenceInput
	{all i:inputAfterSndBlock | one t: precTxFromInput[i] | i.txid = t.txid}


-- 20. input injectivo 
pred propNotSameInput
	{input.~input in iden}


-- 21. as txid dos inputs dos 2 primeiros blocos não coincidem com outras hashes (não referem transações anteriores)
pred propInputsFirst2Blocks 
	{inputsFromBlocks[effectiveBlocks-afterSndBlock].txid in nonUsedHashesMrTxid}


-- 22. um input de uma transação refere um output da transação onde o input foi criado
pred propExemplo
	{all i:inputAfterSndBlock | one o: originTx[i].output | i.value =  o.value and  i.sender = o.to}














-------- predicados para melhor compreesão
-- 1 transação não tem mais que 2 inputs (só para simplificar)
pred propNoMoreThan3Inputs
	{all t:Transaction | #t.input = 1}

-- 1 transação não tem mais que 2 output (só para simplificar)
pred propNoMoreThan3Outputs
	{all t:Transaction | #t.output = 2}

-- output injectivo.
pred propNotSameOutput
	{output.~output in iden}

-- no orpahn transactions 
pred propNoOrpahnTransactions 
	{no orphanTransactions}

-- mais de 3 endereços usados 
pred propMoreThan3UsedAddresses
	{#usedAddresses = 4}

-- mais de 3 valores usados 
pred propMoreThan3UsedValues
	{#usedValues = 4}




fact Facts{
propAtLeastOneInOneOut
propNoOrphanInputs
propNoOrphanOutputs
propAtLeastOneTransaction
propPositiveValues
propDisjMerklerootTxid
propNotSameTxid
propDisjMerklerootTxidInput
propNotSameTx
propNotSameMerkleRoot
--propReferenceTxid
propOrderedTxid
-------Next things---------
propNoConfusionNext
propNoBlocksSameNext
propNoCycleChain
propInitialBlockI
propReachableFromBlockI
-----------------------------
propNotSameTransaction
propNotSameInput
propSequenceInput
propInputsFirst2Blocks
propExemplo





-- melhor compreensao
propNoMoreThan3Inputs
propNoMoreThan3Outputs
propNotSameOutput
propNoOrpahnTransactions
propMoreThan3UsedAddresses

}



-- CREATE TRANSATION


run{
	--#Transaction = 6
	#Tx = #Block 
	#Next = 3
	#Block = 4

 	--#Transaction.fee = 1

} for 30 --but exactly 15 Word

