# Progetto OCaml 2020/21 
## Corso di Programmazione II @UniPi
***
![alt tag](https://img.shields.io/badge/OCaml-NO%20JIT-brightgreen) <br/><br/>
Visita https://try.ocamlpro.com/ per provare il codice in modo REPL.
(Prima l'interprete / typechecker, poi i test, mi raccomando!)

## FAQs
***
1. **Ma si tratta di un JIT?**
_no_. 
2. **Sei __sicuro-sicuro?__**
_si_. 
Dai un'occhiata anche alla relazione, evito di fare un JIT perché all'interno delle chiamate funzionali, viene chiamata una versione della *Apply* pre-compilata, che riceve *evT*, non *espressioni*, quindi durante la eval non viene modificata la struttura sintattica.
