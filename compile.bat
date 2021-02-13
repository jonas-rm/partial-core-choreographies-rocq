echo coqc Basic.v
echo coqc Common.v
echo coqc CC.v
echo coqc Kleene.v
echo coqc Implementation.v
coqc SP.v
coqdoc -g *.v
