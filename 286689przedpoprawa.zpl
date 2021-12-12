#Jakub Zbrzezny, nr indeksu: 286689

#W 4a) tre�� jednak wygl�da: Ka�dy pracownik musi przyj�� minimalny nak�ad pracy w liczbie co najmniej 4.
#Trzeba powybiera� pary dzia��w, kt�re maj� ma�y nak�ad pracy i je wyklucza�.

#---------------- ZBIORY I PARAMETRY ----------------

#Wczytujemy zbi�r pracownik�w.
set P := {read "dane.txt" as "<1n>" comment "#"};

#Wczytujemy zbi�r kod�w dzia��w.
set KD := {read "dane.txt" as "<2n>" comment "#"};

#Wczytujemy zbi�r par (pracownik, kod dzia�u) takich, �e pracownik nie ma nic przeciwko zaj�ciu
#si� danym dzia�em.
set parypkd := {read "dane.txt" as "<1n,2n>" comment "#"}; 

set N:= P*KD - parypkd;
#Zbi�r N jest zbiorem par (pracownik, kod dzia�u) takich, �e pracownik nie chce 
#pracowa� w dziale kd.

#Zbi�r pracownik�w nadzoruj�cych.
set profesorzy := {read "profesorzy.txt" as "<1n>" comment "#"};

#Zbi�r par pracownik�w wymagaj�cych nadzoru.
set nadzorowani := {read "pary.txt" as "<1n,2n>" comment "#"};

#Zbi�r kod�w dzia�u
set kodydzialow := {read "praca.txt" as "<1n>" comment "#"};

#Szacowany nak�ad pracy dla danego dzia�u.
param czas[<i> in kodydzialow] := read "praca.txt" as "<1n>2n" comment "#";

#Zbi�r dni
set T :=  {1..sum<i> in kodydzialow do czas[i]};

#---------------- ZMIENNE ----------------

var czyzajm[P*KD] binary; #Dla pracownika p, kodu dzia�u kd czyzajm[p,kd] = 1
#witw, gdy pracownik p zajmuje si� dzia�em kd.

var nakladpracy[P*KD]; #Nak�ad pracy pracownika p w dziale kd (mo�e przyjmowa�
#warto�ci rzeczywiste).

var maksnaklpracy[P]; #Maksymalny nak�ad pracy pracownika p.

#---------------- FUNKCJA CELU ----------------

#Trzeba zminimalizowa� maksymalny czas pracy przypadaj�cy na pracownika

minimize czaspracy: sum<p,kd> in P*KD do nakladpracy[p,kd];

#---------------- OGRANICZENIA ----------------

#Je�li pracownik p nie zajmuje si� dzia�em kd, to nakladpracy[p,kd] = 0.
subto ogr1: forall<p,kd> in P*KD do nakladpracy[p,kd] <= czyzajm[p,kd] * card(T); 

#Nikt nie zajmuje si� dzia�em, kt�rego nie chce.
subto ogr2: forall<p,kd> in N do czyzajm[p,kd] == 0;

#Ka�dy dzia� musi mie� przypisanych co najmniej 2 pracownik�w.
subto ogr3: forall<kd> in KD do sum<p> in P do czyzajm[p,kd] >= 2;

#�aden pracownik nie mo�e zajmowa� si� wi�cej ni� 5 dzia�ami. 
subto ogr4: forall<p> in P do sum<kd> in KD do czyzajm[p,kd] <= 5;

#Ka�dy pracownik musi przyj�� minimalny nak�ad pracy w liczbie co najmniej 4.
subto ogr5: forall<p> in P do sum<kd> in KD do nakladpracy[p,kd] >= 4;

#Pracownik nie mo�e pracowa� nad 2 dzia�ami o ��cznym nak�adzie pracy mniejszym ni� 3
#(nawet je�eli pracuje r�wnie� nad innymi dzia�ami)
#subto ogr6: forall<p> in P do forall<kd1,kd2> in KD*KD with kd1 != kd2 do nakladpracy[p,kd1] + nakladpracy[p,kd2] >= 3 * (-1 + czyzajm[p,kd1] + czyzajm[p,kd2]);

#Rozpratrujemy pary pracownik�w wymagaj�cych nadzoru.
subto ogr7: forall<p1,p2> in nadzorowani do forall<kd> in KD do -1 + czyzajm[p1,kd] + czyzajm[p2,kd] <= sum<prof> in profesorzy do czyzajm[prof,kd]; 

subto ogr8: forall<p> in P do forall <kd> in KD do maksnaklpracy[p] >= nakladpracy[p,kd];

subto ogr10: forall<p,kd> in P*KD do nakladpracy[p,kd] >= 0;

