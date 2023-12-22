abstract sig Bool{}

one sig True, False extends Bool{} 

sig Transaction{
	i1 : one Signature
}

sig Sender{
	sends : set Transaction,
	privKey : one PrivKey
}

sig PrivKey{
	generates : one PubKey,
	i2 : set Signature
}

sig PubKey{
	i3 : set ValidationFunction
}

sig Signature{
	i4: one ValidationFunction
}

sig ValidationFunction{
	value : one Bool
}

--------------------
-- Predicates
--------------------

-- 1. A assinatura tem que ser feita por uma private key
pred propSamei1i2
	{all s : Sender | s.sends.i1 = s.privKey.i2}

-- 2. A assinatura e public key passam num função de verificação
pred propSamei4i3
	{all s : Sender | s.privKey.i2.i4=s.privKey.generates.i3}

-- 3. Cada remetente envia 2 transações
pred prop2Transactions
	{all s : Sender | #s.sends=2}

-- 4. i1 injetivo
pred propInjectiveI1
	{i1.~i1 in iden}

-- 5. i4 injetivo
pred propInjectiveI4
	{i4.~i4 in iden}

-- 6. privKey injetivo
pred propInjectiveIPrivKey
	{privKey.~privKey in iden}

-- 7. generates injetivo
pred propInjectiveIGenerates
	{generates.~generates in iden}

-- 8. sends injetivo
pred propInjectiveISends
	{sends.~sends in iden}

-- 9. não há private keys orfãs
pred propNoOrphanPrivKeys
	{#Sender = #PrivKey}

-- 10. não há public keys orfãs
pred propNoOrphanPubKeys
	{#PubKey= #PrivKey}


-------------
-- Facts
-------------

fact Facts{

	propSamei1i2

	propSamei4i3

	prop2Transactions

	propInjectiveI1

	propInjectiveI4

	propInjectiveIPrivKey

	propInjectiveIGenerates

	propInjectiveISends

	propNoOrphanPrivKeys

	propNoOrphanPubKeys

}

run {

	#Sender>1

} for 30
