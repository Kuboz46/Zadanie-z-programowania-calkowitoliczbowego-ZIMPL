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
param naklad[<kd> in kodydzialow] := read "praca.txt" as "<1n>2n" comment "#";

#---------------- ZMIENNE ----------------

var czyzajm[P*KD] binary; #Dla pracownika p, kodu dzia�u kd czyzajm[p,kd] = 1
#witw, gdy pracownik p zajmuje si� dzia�em kd.

var czas; #Jest to zmienna rzeczywista b�d�cym g�rnym ograniczeniem czasu ca�ej pracy pracownika p spo�r�d wszystkich pracownik�w p ze zbioru P.

#---------------- FUNKCJA CELU ----------------

#Trzeba zminimalizowa� maksymalny czas pracy przypadaj�cy na pracownika

minimize czaspracy: czas;

#---------------- OGRANICZENIA ----------------

#Nikt nie zajmuje si� dzia�em, kt�rego nie chce.
subto ogr1: forall<p,kd> in N do czyzajm[p,kd] == 0;

#Ka�dy dzia� musi mie� przypisanych co najmniej 2 pracownik�w.
subto ogr2: forall<kd> in KD do sum<p> in P do czyzajm[p,kd] >= 2;

#�aden pracownik nie mo�e zajmowa� si� wi�cej ni� 5 dzia�ami. 
subto ogr3: forall<p> in P do sum<kd> in KD do czyzajm[p,kd] <= 5;

#Ka�dy pracownik musi przyj�� minimalny nak�ad pracy w liczbie co najmniej 4.
subto ogr4: forall<p> in P do sum<kd> in KD do naklad[kd] * czyzajm[p,kd] >= 4;

#Pracownik nie mo�e pracowa� nad 2 dzia�ami o ��cznym nak�adzie pracy mniejszym ni� 3 (nawet, je�eli pracuje r�wnie� nad innymi dzia�ami)
subto ogr5: forall<p> in P do forall<kd1,kd2> in KD*KD with kd1 != kd2 do naklad[kd1] + naklad[kd2] >= 3 * (-1 + czyzajm[p,kd1] + czyzajm[p,kd2]);

#Dla pary pracownik�w (p1, p2) nale��cej do zbioru nadzorowani, je�li pracownicy p1, p2 pracuj� nad tym samym dzia�em, to musi przy nich pracowa� jaki� pracownik nadzoruj�cy.
subto ogr6: forall<p1,p2> in nadzorowani do forall<kd> in KD do -1 + czyzajm[p1,kd] + czyzajm[p2,kd] <= sum<prof> in profesorzy do czyzajm[prof,kd]; 

#Warunek na to, by zmienna czas by�a g�rnym ograniczeniem czasu ca�ej pracy pracownika p spo�r�d wszystkich pracownik�w p ze zbioru P.
subto ogr7: forall<p> in P do sum<kd> in KD do naklad[kd] * czyzajm[p,kd] <= czas;


