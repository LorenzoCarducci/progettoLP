README — Type Checker minimale per Prolog
1. Introduzione

Questo progetto implementa un type checker minimale per Prolog, scritto direttamente in Prolog.
L’obiettivo è analizzare un file .pl, dedurre i tipi dei predicati definiti e verificare che tutti i goal presenti nel programma siano coerenti a livello di tipi.
Il type checker supporta tipi di base, liste, operatori aritmetici e i principali predicati built-in utilizzati nei programmi Prolog introduttivi.
--------------------------------

2.Come si usa

1- bisogna avviare SWI-Prol.
2- spostarti nella cartella in cui si trova il file
3- caricare il tc 
	?- [tc].
4- eseguire il tc sul proprio file 
	?- tc(‘nomefile.pl’).

Es:

?- tc('fact.pl').
%%% Type checking 'fact.pl'.
predicate fact(integer, integer).
Error: Type mismatch: t_atom vs t_int in call 'fact(six,_190)'
true.

-------------------------------

3. Tipi supportati

t_int – intero

t_atom – atomo

t_bool – booleano

t_var(Id) – variabile di tipo generata automaticamente

t_list(T) – lista con elementi di tipo T

t_pred(Name, Arity, ArgsTypes) – tipo dei predicati

--------------------------------

4. Funzionalità implementate

4.1 Inferenza dei tipi 
- deduzione del tipo di ogni argomento dei predicati
- generazione e unificazione delle variabili di tipo
- riconoscimento e gestione delle liste ([], [H|T])
- verifica dei goal e dei loro argomenti

4.2 Built-in supportati
- member/2
- length/2
- append/3
- is_lis/1

4.3 Operatori aritmetici e confronti 
• +, -, *, 
• is
• =:=, =\=, >, <, >=, =< (operatori aritmetici)
• =, \=, ==, \== (operatori logici di unificazione)

4.4 Gestione degli errori 
- Il type checker non si ferma al primo errore 
- li accumula per poi stamparli alla fine 
- quando il tc trova un errore esplicita quali tipi non possono essere 
  unificati perché non hanno senso insieme

--------------------------------------

5. Scelte implementative principali
- il tc non esegue i programmi, si limita ad analizzare i termini prolog 
- le variabili vengono mappate su variabili di tipo (t_var (id)).
- l’analisi genera vincoli che verranno unificati soltanto alla fine del programma 
- le liste vengono rappresentate sempre come t_list(T), dove T è il tipo degli elementi. Tutte le liste usano un’unica forma di tipo.
- l’ambiente dei predicati viene costruito analizzando tutte le clausole nel file. Il tc deve sapere: quante argomentazioni ha, quali tipi aspettarsi, dove è definito nel file    (informazione salvata in pred_env).

-------------------------------------

6. Limitazioni note

- Il type checker è pensato per file che definiscono predicati utente, fatti, regole, aritmetica e liste. Non è pensato per analizzare codice con strutture interne complesse o meta-programmazione.
- Se si esegue tc('tc.pl') compaiono molti errori di tipo, in quanto usa strutture molto generiche (vincoli, sostituzioni, liste di liste, meta-termini).Il sistema di tipi minimale non riesce a tipare queste strutture in modo coerente.
- Il type checker incontra difficoltà nell'analizzare strutture complesse come liste annidate o variabili dentro altre variabili, rendendo complicato determinare i tipi quando queste strutture sono presenti, come nel caso del proprio codice interno.

7. Requisiti

-   SWI-Prolog
