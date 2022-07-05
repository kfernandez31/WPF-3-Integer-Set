# Zadanie 3: Modyfikacja drzew

Zadanie polega na **zmodyfikowaniu biblioteki zbiorów pojedynczych elementów zaimplementowanych jako pewien wariant drzew AVL** (drzewa BST z wyważaniem). 

Dzięki wyważaniu wysokość drzewa jest zawsze rzędu logarytmu z liczby wierzchołków i dlatego wszystkie operacje wykonywane są w czasie logarytmicznym (nawet operacja `split`, ale to jest trochę mniej oczywiste: wynika z tego, że koszt `join` jest w istocie proporcjonalny do różnicy wysokości drzew, które łączymy. A ponieważ na `split` składa się ciąg operacji `join` na coraz wyższych drzewach, ich koszty sumują się do wysokości drzewa razy pewna stała).

Wynikiem modyfikacji ma być **biblioteka zbiorów liczb całkowitych oparta o przedziały**. Czyli elementami występującymi w drzewie muszą być **przedziały**, a nie pojedyncze liczby. Przedziały muszą być rozłączne i w dodatku, aby uniknąć niejednoznaczności reprezentacji, przedziały w drzewie nie mogą być "sąsiednie", czyli np. dwa przedziały $[1,\ldots,3]$ i $[4,\ldots,6]$ powinny być zastąpione przez jeden przedział $[1,\ldots,6]$. 

W naszej bibliotece dopuszczamy przedziały jednoelementowe, np. $[3,\ldots,3]$.

Wszystkie operacje (poza `fold`, `iter`, `elements` oraz `is_empty`) mają wykonywać się w czasie (zamortyzowanym) $O(log n)$, gdzie $n$ jest liczbą wierzchołków w drzewie.

Do zadania dołączona jest oryginalna specyfikacja i implementacja zbiorów (obie dostępne na licencji *GNU Lesser General Public License*) oraz specyfikacja zbiorów przedziałów, której implementację należy przesłać poprzez system moodle jako plik o nazwie [**iSet.ml**](TODO). 

Przy implementacji zwróć uwagę, jak zachowuje się Twój kod dla liczb równych bądź bliskich `max_int` (albo `min_int`). W szczególności konkretne wymaganie dotyczące tego aspektu dla funkcji below podane jest w specyfikacji ([**iSet.mli**](TODO)).

Jak zwykle implementacja powinna być udokumentowana; w szczególności należy wpisać w komentarzu niezmienniki dla używanych struktur danych oraz pre- i post-warunki wszystkich metod występujących w implementacji (zwłaszcza tych, których nazwy nie występują w specyfikacji). Warunki te mogą dotyczyć np. poprawności drzew, zakładanej różnicy wysokości drzew, itp.

Termin wykonania: 2 tygodnie
