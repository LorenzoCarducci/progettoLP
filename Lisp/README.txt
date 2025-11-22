README - Type checker minimale per Common Lisp

1. INTRODUZIONE
    Il programma implementa un type checker semplice, basato sulle idee principali del sistema di tipi di Hindley–Milner, 
    adattato al linguaggio Common Lisp.

    L’obiettivo è:
        - leggere un file .lisp
        - analizzarne le funzioni defun
        - inferire automaticamente il loro tipo
        - controllare che le chiamate di funzione siano coerenti
        - segnalare eventuali errori di tipo in modo chiaro


2. ISTRUZIONI DI UTILIZZO
    Per utilizzare il type checker è sufficiente caricare tc.lisp in un ambiente Common Lisp compatibile e richiamare 
    la funzione:
        (tc "nomefile.lisp")
    il cui argomento sarà il percorso di un qualsiasi file di codice .lisp su cui si vuole eseguire il type checker.

    L’output prodotto comprende:
        - una riga che specifica il file su cui la funzione viene eseguita
        - la stampa dei tipi inferiti per ogni defun
        - eventuali errori

    Il type checker non si ferma al primo errore: processa l’intero file e mostra tutte le anomalie trovate.

    Esempio:
        


3. FUNZIONALITA' IMPLEMENTATE
  3.1 Inferenza dei tipi per defun
    Il programma analizza automaticamente ogni definizione di funzione e:
        - assegna un tipo variabile a ciascun parametro;
        - analizza il corpo della funzione;
        - unifica il tipo del corpo con il tipo di ritorno;
        - supporta parametri con &optional;
        - supporta ricorsione;
        - al termine stampa la firma con ftype.

  3.2 Tipi supportati
    Il sistema gestisce:
        - integer
        - boolean (t/nil)
        - string
        - symbol
        - list(T) — liste omogenee
        - function — con lista argomenti (obbligatori e opzionali) e tipo di ritorno
        - variabili di tipo (:var n)
    Sono presenti:
        - unificazione dei tipi con occurs-check;
        - istanziazione degli schemi di tipo;
        - generalizzazione (polimorfismo limitato).

  3.3 Tipizzazione delle espressioni
    Il type checker gestisce correttamente:
        - letterali
        - simboli
        - quote
        - forme condizionali if
        - chiamate di funzione normali
        - controlli di arità
        - messaggi d’errore chiari in caso di mismatch

  3.4 Supporto per operatori aritmetici e confronti
    Nel tipo ambiente iniziale sono definite le principali primitive aritmetiche e logiche:
        • +, -, *, / :
            integer × integer → integer
        • =, /=, <, <=, >, >= :
            integer × integer → boolean

    Questo permette di rilevare errori come:
        (< "ciao" 3)
        →   Error: "ciao" is not of type 'integer' in call (< "ciao" 3)

  3.5 Gestione “conservativa” di macro e special forms
    Il type checker analizza comunque le sotto-espressioni all’interno di:
        - macro (when, and, or, ecc.)
        - special forms
        - handler-case
        - define-condition
        - format
    ma non impone un tipo preciso all’espressione complessiva.


4. STRUTTURA DEL CODICE E PRINCIPALI SCELTE IMPLEMENTATIVE
  4.1 Scelta del modello di tipo
    È stato adottato un modello ispirato al sistema Hindley–Milner:
        - variabili di tipo generate dinamicamente;
        - unificazione per confrontare i tipi;
        - schemi di tipo per rappresentare funzioni polimorfe;
        - generalizzazione alla chiusura di ogni defun.

  4.2 Ambiente dei tipi (initial-env)
    Al caricamento, viene creato un ambiente di base che contiene:
        - primitive aritmetiche
        - confronti numerici
        - funzioni standard semplici (zerop, 1-)
        - format tipizzato in modo conservativ

  4.3 Gestione degli errori
    Gli errori sono gestiti tramite:
        - un tipo di errore dedicato (tc-error);
        - messaggi chiari che indicano:
            - l’espressione problematica,
            - il tipo atteso,
            - il tipo trovato.

    Il type checker continua dopo un errore, per mostrare tutte le anomalie nel file.


5. LIMITAZIONI NOTE
    - Le lambda expressions non sono trattate come valori di prima classe (ad es. (lambda ...) ritorna un tipo variabile generico).
    - Le forme let, let*, labels non introducono un ambiente locale completo: vengono comunque analizzate nei sottoform, quindi gli errori di tipo emergono.
    - Non viene eseguita una tipizzazione approfondita del condition system (handler-case, define-condition).
    - L’analisi delle liste tramite quote ('(1 2 3)) assume liste omogenee con tipo generico.


6. REQUISITI
    - Interprete Common Lisp (consigliato Lispworks).