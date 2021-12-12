#Jakub Zbrzezny, nr indeksu: 286689

#W 4a) treœæ jednak wygl¹da: Ka¿dy pracownik musi przyj¹æ minimalny nak³ad pracy w liczbie co najmniej 4.
#Trzeba powybieraæ pary dzia³ów, które maj¹ ma³y nak³ad pracy i je wykluczaæ.

#---------------- ZBIORY I PARAMETRY ----------------

#Wczytujemy zbiór pracowników.
set P := {read "dane.txt" as "<1n>" comment "#"};

#Wczytujemy zbiór kodów dzia³ów.
set KD := {read "dane.txt" as "<2n>" comment "#"};

#Wczytujemy zbiór par (pracownik, kod dzia³u) takich, ¿e pracownik nie ma nic przeciwko zajêciu
#siê danym dzia³em.
set parypkd := {read "dane.txt" as "<1n,2n>" comment "#"}; 

set N:= P*KD - parypkd;
#Zbiór N jest zbiorem par (pracownik, kod dzia³u) takich, ¿e pracownik nie chce 
#pracowaæ w dziale kd.

#Zbiór pracowników nadzoruj¹cych.
set profesorzy := {read "profesorzy.txt" as "<1n>" comment "#"};

#Zbiór par pracowników wymagaj¹cych nadzoru.
set nadzorowani := {read "pary.txt" as "<1n,2n>" comment "#"};

#Zbiór kodów dzia³u
set kodydzialow := {read "praca.txt" as "<1n>" comment "#"};

#Szacowany nak³ad pracy dla danego dzia³u.
param czas[<i> in kodydzialow] := read "praca.txt" as "<1n>2n" comment "#";

#Zbiór dni
set T :=  {1..sum<i> in kodydzialow do czas[i]};

#---------------- ZMIENNE ----------------

var czyzajm[P*KD] binary; #Dla pracownika p, kodu dzia³u kd czyzajm[p,kd] = 1
#witw, gdy pracownik p zajmuje siê dzia³em kd.

var nakladpracy[P*KD]; #Nak³ad pracy pracownika p w dziale kd (mo¿e przyjmowaæ
#wartoœci rzeczywiste).

var maksnaklpracy[P]; #Maksymalny nak³ad pracy pracownika p.

#---------------- FUNKCJA CELU ----------------

#Trzeba zminimalizowaæ maksymalny czas pracy przypadaj¹cy na pracownika

minimize czaspracy: sum<p,kd> in P*KD do nakladpracy[p,kd];

#---------------- OGRANICZENIA ----------------

#Jeœli pracownik p nie zajmuje siê dzia³em kd, to nakladpracy[p,kd] = 0.
subto ogr1: forall<p,kd> in P*KD do nakladpracy[p,kd] <= czyzajm[p,kd] * card(T); 

#Nikt nie zajmuje siê dzia³em, którego nie chce.
subto ogr2: forall<p,kd> in N do czyzajm[p,kd] == 0;

#Ka¿dy dzia³ musi mieæ przypisanych co najmniej 2 pracowników.
subto ogr3: forall<kd> in KD do sum<p> in P do czyzajm[p,kd] >= 2;

#¯aden pracownik nie mo¿e zajmowaæ siê wiêcej ni¿ 5 dzia³ami. 
subto ogr4: forall<p> in P do sum<kd> in KD do czyzajm[p,kd] <= 5;

#Ka¿dy pracownik musi przyj¹æ minimalny nak³ad pracy w liczbie co najmniej 4.
subto ogr5: forall<p> in P do sum<kd> in KD do nakladpracy[p,kd] >= 4;

#Pracownik nie mo¿e pracowaæ nad 2 dzia³ami o ³¹cznym nak³adzie pracy mniejszym ni¿ 3
#(nawet je¿eli pracuje równie¿ nad innymi dzia³ami)
#subto ogr6: forall<p> in P do forall<kd1,kd2> in KD*KD with kd1 != kd2 do nakladpracy[p,kd1] + nakladpracy[p,kd2] >= 3 * (-1 + czyzajm[p,kd1] + czyzajm[p,kd2]);

#Rozpratrujemy pary pracowników wymagaj¹cych nadzoru.
subto ogr7: forall<p1,p2> in nadzorowani do forall<kd> in KD do -1 + czyzajm[p1,kd] + czyzajm[p2,kd] <= sum<prof> in profesorzy do czyzajm[prof,kd]; 

subto ogr8: forall<p> in P do forall <kd> in KD do maksnaklpracy[p] >= nakladpracy[p,kd];

subto ogr10: forall<p,kd> in P*KD do nakladpracy[p,kd] >= 0;

