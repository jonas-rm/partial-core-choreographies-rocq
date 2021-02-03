echo coqc Basic.v
coqc Common.v
coqc CC.v
echo coqc Kleene.v
echo coqc Implementation.v
coqc SP.v
coqdoc -g *.v
