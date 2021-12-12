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
param naklad[<kd> in kodydzialow] := read "praca.txt" as "<1n>2n" comment "#";

#---------------- ZMIENNE ----------------

var czyzajm[P*KD] binary; #Dla pracownika p, kodu dzia³u kd czyzajm[p,kd] = 1
#witw, gdy pracownik p zajmuje siê dzia³em kd.

var czas; #Jest to zmienna rzeczywista bêd¹cym górnym ograniczeniem czasu ca³ej pracy pracownika p spoœród wszystkich pracowników p ze zbioru P.

#---------------- FUNKCJA CELU ----------------

#Trzeba zminimalizowaæ maksymalny czas pracy przypadaj¹cy na pracownika

minimize czaspracy: czas;

#---------------- OGRANICZENIA ----------------

#Nikt nie zajmuje siê dzia³em, którego nie chce.
subto ogr1: forall<p,kd> in N do czyzajm[p,kd] == 0;

#Ka¿dy dzia³ musi mieæ przypisanych co najmniej 2 pracowników.
subto ogr2: forall<kd> in KD do sum<p> in P do czyzajm[p,kd] >= 2;

#¯aden pracownik nie mo¿e zajmowaæ siê wiêcej ni¿ 5 dzia³ami. 
subto ogr3: forall<p> in P do sum<kd> in KD do czyzajm[p,kd] <= 5;

#Ka¿dy pracownik musi przyj¹æ minimalny nak³ad pracy w liczbie co najmniej 4.
subto ogr4: forall<p> in P do sum<kd> in KD do naklad[kd] * czyzajm[p,kd] >= 4;

#Pracownik nie mo¿e pracowaæ nad 2 dzia³ami o ³¹cznym nak³adzie pracy mniejszym ni¿ 3 (nawet, je¿eli pracuje równie¿ nad innymi dzia³ami)
subto ogr5: forall<p> in P do forall<kd1,kd2> in KD*KD with kd1 != kd2 do naklad[kd1] + naklad[kd2] >= 3 * (-1 + czyzajm[p,kd1] + czyzajm[p,kd2]);

#Dla pary pracowników (p1, p2) nale¿¹cej do zbioru nadzorowani, jeœli pracownicy p1, p2 pracuj¹ nad tym samym dzia³em, to musi przy nich pracowaæ jakiœ pracownik nadzoruj¹cy.
subto ogr6: forall<p1,p2> in nadzorowani do forall<kd> in KD do -1 + czyzajm[p1,kd] + czyzajm[p2,kd] <= sum<prof> in profesorzy do czyzajm[prof,kd]; 

#Warunek na to, by zmienna czas by³a górnym ograniczeniem czasu ca³ej pracy pracownika p spoœród wszystkich pracowników p ze zbioru P.
subto ogr7: forall<p> in P do sum<kd> in KD do naklad[kd] * czyzajm[p,kd] <= czas;


