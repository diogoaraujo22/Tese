-----------------------
--Structure
-----------------------

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
	i3 : set Signature
}
sig Signature{
	validationFunction: one Bool
}
sig ValidationFunction{}


fact connectSigs {
	
	all s : Sender | s.sends.i1 = s.privKey.i2
	all s : Sender | s.privKey.i2=s.privKey.generates.i3

	all s : Sender | some s.sends

	i1.~i1 in iden
	privKey.~privKey in iden
	generates.~generates in iden
	sends.~sends in iden

	#Sender>1
	#Sender = #PrivKey
	#PubKey= #PrivKey


}

run {} for 20
