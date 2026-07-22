#import "@preview/classicthesis:0.1.0": *

#show: classicthesis.with(
  title: "Topološka analiza\npodataka",
  // subtitle: "A Subtitle for Your Work",
  author: "Jovana Lazić 21/2022\nLazar Jovanović 69/2022",
  date: "Jun 2026.",
  // Optional: dedication and abstract
  // dedication: [To those who seek elegant typography.],
  // abstract: [This is the abstract of your work...],
)

// ============================================================================
// Part I
// ============================================================================

= Uvod

Topologija je grana matematike nastala apstrahovanjem metrike iz metričkog 
prostora ostavivši iza sebe samo opšti pojam bliskosti. Ugrubo se bavi 
klasifikovanjem skupova po različitim inherentnim osobinama tih skupova -
tzv. topološkim invarijantama. 

#definition()[
  Uređen par $(X, tau_X)$ koji čine neprazan skup $X$ i kolekcija svih 
  otvorenih podskupova sadržanih u njemu $tau_X$ zovemo _topološkim prostorom_.
]

#remark()[
  $tau_X$ zovemo _topologijom prostora_. Često i sam skup $X$ zovemo topološkim 
  prostorom kada je $tau_X$ implicitno zadato ili poznato. 
]

#definition()[
  Funkciju $f: X arrow Y$ zovemo _neprekidnom_ ako $(forall y subset tau_Y) f^(-1)(y) subset tau_X$.
  Odnosno, ako je inverzna slika svakog otvorenog skupa u $Y$ otvoren skup u $X$.
]

#definition()[
  Ako za topološke prostore $X$ i $Y$ postoji preslikavanje $f: X arrow Y$ takvo da važi:
  + $f$ je neprekidna funkcija
  + $f$ je bijekcija
  + $f^(-1)$ je neprekidna funkcija
  tada za $X$ i $Y$ kažemo da su _homeomorfni_ u oznaci $X approx Y$ a $f$ zovemo _homeomorfizam_.
]

Svaka osobina prostora koja je invarijanta u odnosnu na homeomorfizme zovemo _topološkim invarijantama_.
Ispostaviće se da baš one hvataju našu intuiciju o oblicima (mada je neretko i ruše). Svaki trougao 
nezavisno od geometrijske realizacije (kako ga nacrtamo) će ostati trougao te po mnogo čemu biti 
sličan bilo kom drugom trouglu na koji možemo naići. Topološka analiza podataka se upravo bavi 
ekstrahovanjem značajnih topoloških invarijanti prostora podataka na osnovu kojih se prave bolji 
klasifikatori. U cilju izračunavanja topoloških invarijanti, služićemo se algebarskom topologijom.

Proći ćemo dve najčešće metode topološke analize podataka:
+ perzistentnu homologiju
+ mapper algoritam

U nastavku podrazumevamo da radimo sa očišćenim podacima koji žive u $RR^n$. Biblioteka računarske 
topologije koju ćemo koristiti je #link("https://github.com/giotto-ai/giotto-tda", "Giotto TDA").

= Perzistentna homologija

== Osnovna ideja 
Homologija prostora ima za cilj da uhvati "rupe" tog prostora određene dimenzije. 
Kako znamo da se nalazimo u nekom potprostoru od $RR^n$, najveća moguća dimenzija
rupe će biti za jedan manja odnosno $n-1$. U praksi, retko kada se traže rupe 
dimenzije veće od 1 a skoro nikad veće od 2, kako zbog računske složenosti, tako 
i zbog do sada ne dokazanog benefita same potrage. 

Naći rupu u nekakvom opštem prostoru koji nam nije unapred zadat niti ga savršeno
opažamo ne možemo ni u jednom smislu naći direktno. Potrebno nam je nekakvo 
pojednostavljenje koje će ipak zadržati to što tražimo. Odnosno, potrebno nam je 
da naša definicija rupe bude topološka invarijanta kao i homeomorfan prostor u kome 
znamo da je nađemo. Ispostavilo se da su _simplicijalni kompleksi_ pogodni u ove svrhe.

#definition()[
  Neka su $u_0, u_1, ... u_k in RR^n$. Tačku $x = sum_(i=0)^k lambda_i u_i$ za $lambda_i in RR$
  nazivamo _afinom kombinacijom_. Za tačke $u_i$ kažemo da su _afino nezavisne_ odnosno u _opštem
  položaju_ ako su vektori $u_i - u_0, i=1..k$ linearno nezavisni. Afinu kombinaciju u kojoj su 
  $lambda_i >= 0$ zovemo _konveksnom kombinacijom_.
]

#definition()[
  _k-simpleks_ $sigma$ jeste skup svih konveksnih kombinacija $k+1$ afino nezavisnih tačaka u
  oznaci $sigma = "conv"{u_0, u_1, ... u_k}$. Dimenzija simpleksa je $dim sigma = k$.
]

#definition()[
  Ako je $sigma = "conv"{u_0, u_1, ... u_k}$ simpleks i ${v_0, v_1, ... v_l} subset.eq {u_0, u_1, ... u_k}$
  tada je $tau = "conv"{v_0, v_1, ... v_l}$ stranica simpleksa $sigma$ u oznaci $tau <= sigma$.
]

#definition()[
  _Simplicijalni kompleks_ jeste konačna kolekcija simpleksa $K$ takva da:
  + $(forall sigma in K)(forall tau <= sigma) tau in K$
  + $(forall sigma, tau in K) sigma inter tau = emptyset or sigma inter tau <= sigma, tau$
  Odnosno, svaka stranica svakog simpleksa simplicijalnog kompleksa jeste simpleks tog 
  simplicijalnog kompleksa i svaka dva simpleksa u kompleksu su ili disjunktna ili imaju 
  zajedničku stranu. Dimenzija simplicijalnog kompleksa $dim K = max {dim sigma | sigma in K}$.
]

Kako naši podaci žive u $RR^n$ i formiraju tzv. _oblak tačaka_ (point cloud), a mi želimo da radimo
sa simplicijalnim kompleksima, potrebno je nekako preći iz jednog oblika u drugi. Zapravo, oblak tačaka
jeste jedan simplicijalni kompleks jer je svaka tačka simpleks za sebe. Jasno je doduše da takav 
kompleks ne nosi sa sobom puno značajne informacije o bilo kakvim rupama (naime, rupa nema). Da li onda 
možemo nekako grupisati tačke u veće simplekse pa tu pronaći rupe? Koliko uopšte treba povećavati simplekse
i kojim rupama uopšte dati na značaju dok nastaju i nestaju? Odgovori na sva ova pitanja nam zapravo daju
samu tehniku koju razmatramo. 

Prvi sastojak je odabir kompleksa. 
#definition()[
  Neka je $S subset RR^n$ neki skup tačaka i $r in RR$. _Vietoris-Ripsov_ kompleks je: \
  $"VR"(r):={sigma subset.eq S | "diam"(sigma) <= 2r}$. Odnosno, to je simplicijalni kompleks 
  izgrađen od simpleksa koji svi staju u lopte poluprečnika $r$.
]

#show figure.caption: it => it.body

#grid(
  columns: 2,
  gutter: 10pt,
  figure(
    rect(image("images/vr0.png", width: 100%)),
    caption: "VR(0)"
  ),
  figure(
    rect(image("images/vr3.2.png", width: 100%)),
      caption: "VR(3.2)"
  ),
  figure(
    rect(image("images/vr4.5.png", width: 100%)),
      caption: "VR(4.5)"
  ),
  figure(
    rect(image("images/vr7.png", width: 100%)),
      caption: "VR(7)"
  )
)

Slike su napravljene pomoću #link("https://www.geogebra.org/m/ye79r6ws", "geogebra apleta").
 
Drugi sastojak je pojam _filtracije_. Primetimo da je $"VR"(0)$ samo naš polazni oblak tačaka dok
je $"VR"(infinity)$ zapravo samo jedan simpleks unutar kompleksa. Kako je sam oblak tačaka konačan, tako 
će i broj potrebnih koraka (odnosno parametara $r_1, r_2...$) biti konačan. Filtracijom ćemo zvati
niz kompleksa $K_0 subset.eq K_1 subset.eq K_2 subset.eq ... subset.eq K_n$ koji smo dobili povećavanjem
parametra $r$. Nije nužno da kompleks koji koristimo bude baš Vietoris-Ripsov, koriste se i Čehov i Alfa
kompleks.

Poslednji sastojak dobijamo odgovorom na pitanje koje rupe treba da vrednujemo: one koje najduže 
opstanu. Otuda i naziv i poenta same metode. Ostaje još definisati homologiju simplicijalnog kompleksa
i način da je izračunamo. 

#definition()[
  Lančasti kompleks $(C_*, d_*)$ jeste kolekcija Abelovih grupa $C_* = {C_n}_(n in ZZ)$ zajedno
  sa familijom preslikavanja $d_*: {d_n: C_n arrow C_(n-1)}_(n in ZZ)$ takvih da je
  $d_(n-1) circle d_n = 0, forall n in ZZ$.
]

#definition()[
  Neka je $(C_*, d_*)$ lančasti kompleks i neka je $n$ ceo broj. $Z_n = ker d_n$ i $B_n = im d_(n+1)$
  zvaćemo n-ciklovima i n-granicama.
]

#remark()[
  Iz algebre znamo da $Z_n, B_n <= C_n$ a dodatno važi i $B_n <= Z_n$ jer $d_n circle d_(n+1) = 0$.
]

#definition()[
  _n-ta homologija_ lančastog kompleksa $(C_*, d_*)$ jeste $H_n (C_*) = Z_n \/ B_n$
]

Homologija simplicijalnih kompleksa se definiše preko homologije lančastih 
kompleksa (koje nećemo za sada komentarisati) te ih moramo uvesti. U nastavku 
podrazumevamo da je $K$ simplicijalni kompleks, $n in NN_0$ i $G$ grupa.

#definition()[
  n-lanac sa koeficijentima u $G$ je formalna suma n-simpleksa odnosno
  $c = sum_(i=1)^k a_i sigma_i$ gde je $dim sigma_i = n$ i $a_i in G$. Za dva n-lanca
  $c_1 = sum_(i=1)^k a_i sigma_i$ i
  $c_2 = sum_(i=1)^k b_i sigma_i$ definišemo
  $c_1 + c_2 = sum_(i=1)^k (a_i + b_i) sigma_i$ kao i 
  $0 = sum_(i=1)^k 0 sigma_i$.
  Sa $C_n$ obeležimo grupu n-lanaca nastalu na ovaj način.
]

#definition()[
  Definišimo $d_n: C_n arrow C_(n-1)$ nad generatorima n-lanaca grupe $C_n$ kao \
  $d_n(sigma) = sum_(i=0)^k (-1)^i [u_0, u_1, ... hat(u_i), ... u_k]$ gde su $u_i$
  0-simpleksi (tačke) simplicijalnog kompleksa K a sa $hat(u_i)$ označavamo da smo
  izbacili i-to teme.
]

#theorem()[
  Ovako definisani $(C_*, d_*)$ formiraju lančasti kompleks.
]

#definition()[
  Homološke grupe simplicijalnog kompleksa $K$ definišemo kao homološke grupe lančastog kompleksa
  određenog sa $K$. 
]

Kakve ovo veze ima s rupama? Ideja je u tome da umesto da tražimo samu rupu, mi nađemo njen obod.
Operator $d_n$ je zapravo operator granice u dimenziji $n$. Smisao uslova $d_n circle d_(n-1) = 0$
leži u činjenici da granica granice jedne dimenzije mora biti trivijalna. Zašto $Z_n$ sečemo sa $B_n$?
$Z_n$ čini grupu svih elemenata koji graničnim operatorom idu u nulu ali elementi koji su činili granicu
u prethodnoj dimenziji nužno idu u nulu te u tom smislu nisu bitni. Ono što nam ostaje u količničkoj 
grupi su zapravo n-lanci koji nisu granica ničega. Odnosno, oni su baš granica rupe.

#definition(title: "Betijevi brojevi")[
  $beta_n = "rank" H_n$
]

U praksi se za $G$ uzima grupa $ZZ_2$. Prednost je ta što je izuzetno lako i brzo za računanje 
koeficijenata kao i Betijevih brojeva.

== Igračka primer

Prvi primer da se uverimo da sve ovo možda nečemu služi jeste da klasifikujemo neke osnovne 
topološke prostore po hjihovim homološkim grupama. Klasifikovaćemo kružnice $S^1$, sfere $S^2$
i toruse $T^2$.

#figure(
  rect(
    table(
      columns: (auto, auto, auto, auto),
      table.header([*Prostor*], [*$H_0$*], [*$H_1$*], [*$H_2$*]),
      [$S^1$], [$ZZ$], [$ZZ$], [$0$],
      [$S^2$], [$ZZ$], [$0$], [$ZZ$],
      [$T^2$], [$ZZ$], [$ZZ plus.o ZZ$], [$ZZ$],
    )
  ),
  caption: [Homološke grupe $S^1$, $S^2$ i $T^2$],
)

Ovo je dobro mesto na konkretnom primeru da vidimo šta svaka homološka grupa zapravo znači.
$H_0$ konkretno broji komponente povezanosti prostora. Svako $ZZ$ koje učestvuje u direktnoj
sumi kojoj je $H_0$ izomorfna odgovara jednoj komponenti povezanosti. Kao što vidimo iz tabele,
sva tri prostora imaju samo jedno $ZZ$ odnosno jednu komponentu povezanosti što i očekujemo. 
Samim tim, nije nam potrebno da je izračunamo da bismo razlikovali ove prostore ali to
svakako uraditi da se uverimo. \
$H_1$ je prva prava rupa i misli se na jednodimenzionu rupu, baš onakvu kakvu kružnica zatvara.
Sfera $S^2$ nema nijednu 
kružnicu koju ne možemo da skupimo u tačku pa je njena $H_2$ trivijalna. Torus $T^2$ ima dve 
takve disjunktne klase kružnica:
+ prva ide oko unutrašnjosti torusa
+ druga ide oko centra torusa
Kružnica $S^1$ je dvodimenzion prostor pa samim tim ne može imati dvodimenzionu rupu. Sfera $S^2$
i torus $T^2$ oba zatvaraju po jednu trodimenzionu šupljinu.

Vietoris-Ripsov perzistentni dijagram pravimo na sledeći način:
```python
from gtda.homology import VietorisRipsPersistence

VR = VietorisRipsPersistence(homology_dimensions=[0, 1, 2])
diagrams = VR.fit_transform(point_clouds)
```

Dijagrami su grafici na kojima se za svaku homološku grupu koju smo naveli beleže vreme nastajanja 
(birth) i vreme umiranja (death) izražene preko vrednosti parametra $r$ Vietoris-Ripsovog kompleksa.
Dijagrami sami za sebe nisu pogodni kao feature za klasifikator te ćemo koristiti _perzistentnu entropiju_.
#definition()[
  Za perzistentni dijagram $D = {(b_i, d_i) | d_i eq.not infinity}_(i in I)$, perzistentna entropija jeste \ 
  $E(D) := - sum_(i in I) p_i log p_i$ gde je $p_i := (d_i - b_i) / (sum_(j in I) d_j - b_j)$
]

Perzistentnu entropiju računamo lako:
```python
from gtda.diagrams import PersistenceEntropy

PE = PersistenceEntropy()
features = PE.fit_transform(diagrams)
```

Features ostaje samo matrica brojeva koja je pogodna za treniranje klasifikatora na koje smo navikli.
Koristićemo `RandomForestClassifer` iz sklearn biblioteke.

U pratećem jupyter notebooku vidimo da i sa i bez uključivanja $H_0$ model bez greške razlikuje 
oblike, što si očekuje na ovakom primeru.

== MNIST
I ako jeste mačiji kašalj za konvolutivne neuronske mreže (CNN), problem prepoznavanja rukom pisanih 
cifara sa slika nije naivan problem i uglavnom se ne rešava dobro klasičnim metodama mašinskog 
učenja. Međutim, eksploatacijom perzistentne homologije, moguće je dobiti 
#link("https://arxiv.org/pdf/1910.08345", "pristojne rezultate").
Jedna implementaciju rada se nalazi #link("https://github.com/giotto-ai/giotto-tda/blob/master/examples/MNIST_classification.ipynb", "ovde").

= Mapper algoritam

== Osnovna ideja 
Mapper algoritam služi da prevede visokodimenzione point cloudove u grafovsku reprezentaciju
koja je dovoljno male dimenzije da bude pogodna za vizualizaciju ili samo treniranje modela. 
Sastoji se od četiri suštinska koraka:
+ filtracija - nekim od postojećih algoritama redukcije dimenzionalnosti (često PCA) podatke 
               spuštamo u nižu dimenziju (često 1 ili 2)
+ binovanje - delimo dobijen prostor niže dimenzije u preklapajuće intervale (odnosno pravimo
              konačan pokrivač nad podacima)
+ klusterizacija - tačke pojedinačnih intervala klasterujemo na osnovu njihovih visokodimenzionih
                   osobina iz polaznog skupa podataka
+ konstrukcija grafa - svaki klaster je čvor a ivice dodajemo između svih klastera koji imaju 
                       zajedniču tačku (to je moguće zbog načina na koji smo podelili intervale)

== Pubmed
Demonstriraćemo moć i bolje pojasniti teorijske osnove samog algoritma nad skupom podataka _PubMed_.
U pitanju je kolekcija naučnih članaka iz oblasti medicine koji su povezani citatima a predstavljeni
svojim tf-idf vektorom. Najčešći zadatak nad ovim skupom jeste klasifikacija. Najsavremeniji 
pristup rešavanju ovog zadatka nad ovim skupom podataka pružaju grafovske neuronske mreže (GNN)
zasnovane na metodu prosleđivanja poruka (message passing). Koliko god pokušavali, klasičnim 
metodama uz dodatak TDA ga nećemo nadmašiti no to i nije toliko strašno jer ga ništa u skorije 
vreme ni neće nadmašiti. 

PubMedu se može pristupiti bez ikakve upotrebe topologije podataka i to ćemo koristiti kao 
polaznu tačku. Cilj je da ispitamo koliko povezanost odnosno citati mogu doprineti konačnom 
modelu. Za tu početnu ocenu ćemo uzeti bolji između `SVC` i
`RandomForestClassifier` iz sklearn biblioteke. Vidimo da je slučajna šuma nešto malo bolja 
od metode potpornih vektora. Naravno, mogu se modeli dodatno štelovati pretragom po rešetki 
(grid search) no to nije poenta te se nećemo zadržavati.

== Primena mapper algoritma
Videli smo u uvodu da imamo određene izbore da napravimo kada koristimo mapper. Prvi je 
filter funkcija koja se nekad zove i sočivo (lens). Kako imamo suštinski dva različita 
modaliteta podataka (tf-idf vektore i strukturu citata), deluje smisleno da redukujemo 
podatke u dve dimenzije: jednu po modalitetu. 

Prva dimenzija će biti PageRank čvora a druga najveća SVD komponenta tf-idf matrice.
Pošto radimo sa grafom od 19000 čvorova, neke komplikovanije osobine kao što je 
centralnost nisu praktične. PageRank se računa relativno brzo a istorijski jeste
informativna karakteristika čvora. SVD/PCA nad tf-idf matricom je relativno česta
stvar koju verujem da nema potrebe objašnjavati (latentna semantička analiza). 

Drugi izbor koji pravimo jeste odabir intervala. Ovo je deo koji zahteva malo sreće 
ili malo pretrage po rešetki (grid search) koju suštinski nije moguće uraditi u nekom
normalnom vremenskom roku zbog trajanja izvršavanja jednog prolaza kroz algoritam. Ipak,
probali smo više kombinacija, nije se ispostavilo da pravi značajnu razliku.

Treći izbor je odabir algoritma klasterovanja i njegovih parametara. U literaturi se 
najčešće koristi DBScan. To je iz razloga što ne pravi jake pretpostavke o obliku 
podataka za razliku od drugih metoda (recimo k-means koji pretpostavlja globularne klastere).
Odabir za epsilon i broj instanci bi trebalo potkrepiti ponovo pretragom po rešetki koju
ne možemo uraditi u razumnom vremenu te smo probali par kombinacija bez nekog naročitog 
boljitka. Metrika koju ćemo koristi je kombinovana metrika pojedinačnih koordinata:\
$D(X, Y) := alpha D_G(X, Y) + (1 - alpha) D_T(X, Y)$\
gde je $D_G$ najkraće netežinsko rastojanje od $X$ do $Y$ dok je $D_T$ kosinusno rastojanje
tf-idf reprezentacija čvorova. Uzeli smo $alpha=0.4$ logikom da je sadržaj samog rada bitniji
od toga ko ga citira. 

Finalni kod za ovaj konkretan pipeline ima puno tehničkih detalja koji nisu naročito 
zanimljivi za objašnjavanje a ni previše bitni. Konačan graf koji smo dobili mapper 
algoritmom je:

#image("images/mapper.png")

Boje označavaju koliko se dobro agregirani radovi slažu sa prvom SVD komponentom 
tf-idf matrice koju smo koristili prilikom filtriranja. Što je broj veći, više 
prate najopštiju semantičku temu prisutnu u podacima. Odnosno, što je broj manji,
to pričamo o specifičnijim radovima koji verovatno koriste neki vrlo usko specifični
žargon i slično.

Pristustvo jedne velike komponente povezanosti okružene mnoštvom manjih signalizira 
da imamo jednu veliku bazu dobro semantički i strukturno povezanih radova kao i dobar 
broj manjih samostalnih zajednica. Ovo mogu biti i klasteri od po jednog dva rada 
koji nisu mnogo citirani ili radovi koji koriste reči koje su se pojavile izuzetno 
mali broj puta i slično. Ono što nam se ne sviđa u ovom grafu jeste što ništa od ovoga
nije naročito neočekivano. Kada bismo morali da nagađamo kako izgleda, nešto bismo 
ovako i zamišljali. U kontekstu konvertovanja samog grafa u nove feature-e kojim 
bismo pojačali našu slučajnu šumu, ne nadamo se previše.

Kako uopšte da napravimo neki feature od ovog grafa?

Ovo nije jednostavno pitanje i može verovatno još jedan ceo tekst da se napiše 
koji obrađuje samo njega. Umesto toga, možemo primetiti da svaki dokument pripada 
jednom ili više čvorova mapper grafa i samu tu pripadnost možemo tretirati kao 
feature-e. 

Konačno, kada uporedimo metrike slučajne šume sa i bez našeg silnog truda, vidimo 
da ispada bolje da nismo ništa radili.

Zašto?

Odgovor leži u sledećem: sami feature-i ne pružaju značajno veću količinu informacije
u odnosu na njihovu veličinu. Naime, što više parametara stablo odlučivanja pa samim tim
i nasumična šuma ima na raspolaganju, to im je teže da naprave dobra razdvajanja prostora.
Kada pogledamo najvažnije feature-e jedne i druge šume, primećujemo da su skoro pa isti
osim što u novoj šumi imamo i naše topološke feature-e koji očito ne generalizuju dobro 
na test podacima.

Sam mapper algoritam ima zaista veliku primenu u nauci, samo očito zahteva malo više 
znanja da bi se dobro iskoristio. 

= Perzistentna homologija na PubMed skupu

Mapper nam je dao jedan topološki pogled na PubMed. Prirodno je zapitati se da li i
perzistentna homologija, drugi stub topološke analize podataka, može da izvuče
korisnu informaciju iz istog skupa. Za razliku od igračka primera iz druge glave, gde
smo klasifikovali cele oblake tačaka (kružnice, sfere, toruse), ovde je zadatak
klasifikacija čvorova (radova), pa nam trebaju topološke karakteristike po čvoru,
analogne pripadnostima mapper grafu iz prethodne glave.

== Lokalna perzistentna homologija okolina
Za svaki rad $i$ posmatramo njegovu citatnu okolinu, to jest sam rad zajedno sa svim
radovima sa kojima je povezan citatom. Tf-idf vektori te okoline čine mali oblak tačaka
u $RR^500$ nad kojim gradimo Vietoris-Ripsov perzistentni dijagram (dimenzije 0 i 1),
koristeći kosinusno rastojanje $D_T$ isto kao u mapper poglavlju. Iz dobijenog dijagrama
izvlačimo šest karakteristika po čvoru:
- logaritam stepena čvora (veličina okoline),
- perzistentnu entropiju u dimenziji 0 i 1 ($"PE"_(H_0)$, $"PE"_(H_1)$),
- broj i najveću trajnost jednodimenzionih rupa,
- ukupnu trajnost nula-dimenzionih klasa (mera raširenosti okoline).

Perzistentnu entropiju uvodimo isto kao u drugoj glavi, ona sažima raspodelu trajnosti
u dijagramu u jedan broj. Ceo proračun za svih 19717 čvorova traje svega nekoliko sekundi
jer su okoline male.

#figure(
  image("images/ph_diagram_example.png", width: 60%),
  caption: [Perzistentni dijagram citatne okoline jednog rada. $H_0$ tačke leže na osi
  $"birth"=0$, a $H_1$ tačke su nagurane uz dijagonalu, kratkoživeće petlje bez izražene rupe.]
)

Već sam dijagram nagoveštava problem: jednodimenzione klase ($H_1$) skoro sve leže tik
uz dijagonalu, što znači da su to kratkoživeće petlje (topološki šum), a ne stvarne rupe u
podacima. Citatne okoline u tf-idf prostoru nemaju bogatu topologiju.

== Poređenje modela
Kao i kod mappera, polazna tačka su `RandomForestClassifier` i `SVC` na čistim tf-idf
vektorima, a zatim tf-idf-u dodajemo šest topoloških karakteristika. Sve modele
ocenjujemo na istoj train/test podeli (`random_state=42`, 20% za test, 3944 radova).
Za razliku od koda iz mapper sveske koji je štampao binarnu konfuzionu matricu, ovde
dajemo pravu višeklasnu ocenu po sve tri klase.

#figure(
  rect(table(
    columns: (auto, auto, auto),
    table.header([*Model*], [*Tačnost*], [*Makro F1*]),
    [RF na tf-idf], [0.8884], [0.8871],
    [SVC na tf-idf], [0.8798], [0.8794],
    [RF samo na PH karakteristikama], [0.4108], [0.3207],
    [RF na tf-idf + PH], [*0.8935*], [*0.8924*],
  )),
  caption: [Ukupno poređenje na fiksnoj podeli.],
)

Same PH karakteristike nose vrlo malo informacija, model treniran isključivo na njima
jedva prevazilazi pogađanje većinske klase (koja čini oko 40% skupa). U kombinaciji sa
tf-idf-om, na ovoj podeli, kombinovani model deluje malo bolji od baseline-a, i to
ravnomerno po svim klasama:

#figure(
  rect(table(
    columns: (auto, auto, auto, auto),
    table.header([*Klasa*], [*F1 (tf-idf)*], [*F1 (tf-idf + PH)*], [*Razlika*]),
    [Klasa 0], [0.8803], [0.8867], [+0.0064],
    [Klasa 1], [0.8988], [0.9057], [+0.0069],
    [Klasa 2], [0.8823], [0.8848], [+0.0025],
  )),
  caption: [F1 mera po klasama na fiksnoj podeli.],
)

#figure(
  image("images/ph_perclass_f1.png", width: 65%),
  caption: [F1 po klasama: baseline naspram dodatih PH karakteristika (fiksna podela).]
)

== Da li je poboljšanje stvarno?
Razlika od pola procenta je vrlo mala i lako može biti posledica jednog povoljnog izbora podele. Zato radimo uparenu unakrsnu validaciju (`RepeatedStratifiedKFold`, 5 foldova
puta 2 ponavljanja): u svakom foldu treniramo oba modela na istim podacima i poredimo ih
uparenim t-testom.

#figure(
  rect(table(
    columns: (auto, auto, auto),
    table.header([*Model*], [*Tačnost (μ ± σ)*], [*Makro F1 (μ ± σ)*]),
    [RF na tf-idf], [0.8922 ± 0.0041], [0.8915 ± 0.0047],
    [RF na tf-idf + PH], [0.8906 ± 0.0047], [0.8897 ± 0.0051],
  )),
  caption: [Unakrsna validacija preko 10 foldova.],
)

Pod unakrsnom validacijom rezultat je drugačiji: prosečna razlika u tačnosti je zapravo
negativna ($-0.0016$), kombinovani model je bolji u samo 5 od 10 foldova, a upareni
t-test daje $p = 0.15$ za tačnost i $p = 0.11$ za makro F1. Dakle, nema statistički
značajne razlike. Prividno poboljšanje sa fiksne podele bilo je šum.

Zašto PH karakteristike ne pomažu? Odgovor se vidi u njihovim raspodelama po klasama:

#figure(
  image("images/ph_features_by_class.png", width: 85%),
  caption: [Raspodela dve najznačajnije PH karakteristike po klasama, gotovo identične.]
)

Raspodele su praktično iste za sve tri klase, pa karakteristike ne mogu da razdvoje
klase. Uz to, u kombinovanom modelu ukupan udeo svih šest PH karakteristika u značaju
slučajne šume je svega oko 1%. Dodavanjem šest neinformativnih kolona uz 500 tf-idf
kolona samo unosimo malo šuma.

Do sada smo topologiju gradili iz tf-idf rastojanja suseda, dakle iz semantike, a ne iz
same mreže citata. Ostaje najzanimljivije pitanje: da li sama struktura ko-koga-citira nosi
signal o klasi?

== Strukturna perzistentna homologija citatnih mreža
Ovde gradimo topologiju isključivo iz žica citata. Za svaki rad uzimamo njegovu 2-hop
citatnu ego-mrežu (rad, radovi sa kojima je povezan, i njihovi susedi), računamo
graf-geodezijsko rastojanje unutar tog podgrafa i nad njim Vietoris-Ripsov perzistentni
dijagram. Sada $H_1$ hvata citatne petlje, obrasce oblika $i arrow a arrow c arrow b arrow i$,
odnosno da li se susedi jednog rada i međusobno citiraju.

Zanimljiv detalj: 1-hop ego-mreže su gotovo uvek stabla (nijedna nema $H_1$ petlju, jer se
trougao u perzistenciji odmah "popuni"), pa tek 2-hop okolina otkriva prave petlje. Veličinu
podgrafa ograničavamo na 150 radova zbog čvorova sa ogromnim brojem citata.

#figure(
  image("images/struct_diagram_example.png", width: 58%),
  caption: [Strukturni dijagram jedne guste citatne ego-mreže. Geodezijska rastojanja su
  celobrojna pa se tačke gomilaju; $×n$ označava koliko klasa se poklopi. Ovaj rad ima preko
  200 nezavisnih citatnih petlji.]
)

Za razliku od semantičke PH, strukturne petlje nisu retke: 44% radova ima bar jednu
$H_1$ petlju u svojoj 2-hop citatnoj mreži. Zanimljivo je da strukturne karakteristike i same nose vidljiv signal:

#figure(
  rect(table(
    columns: (auto, auto, auto),
    table.header([*Model*], [*Tačnost*], [*Makro F1*]),
    [Većinska klasa (referenca)], [~0.40], [--],
    [RF samo na semantičkim PH], [0.4108], [0.3207],
    [RF samo na strukturnim PH], [*0.4990*], [*0.4570*],
  )),
  caption: [Sam topološki signal: strukturna PH je osetno iznad većinske klase.],
)

Strukturna PH sama dostiže tačnost oko 0.50, znatno iznad većinske klase (~0.40) i iznad
semantičke PH (0.41). Dakle sama mreža citata nosi informaciju o klasi. To se vidi i u
raspodeli po klasama: klasa 0 ima mnogo manje citatnih petlji od klasa 1 i 2, jer su joj
citatne mreže ređe (prosečan stepen 2.5 naspram 3.8 i 4.0).

#figure(
  image("images/struct_features_by_class.png", width: 85%),
  caption: [Broj petlji i perzistentna entropija $H_1$ po klasama, gde je klasa 0 vidno stablastija.]
)

Pa ipak, kada strukturne karakteristike dodamo tf-idf-u i proverimo unakrsnom validacijom,
rezultat je isti kao ranije:

#figure(
  rect(table(
    columns: (auto, auto, auto),
    table.header([*Model*], [*Tačnost (μ ± σ)*], [*Makro F1 (μ ± σ)*]),
    [RF na tf-idf], [0.8922 ± 0.0041], [0.8915 ± 0.0047],
    [RF na tf-idf + strukturna PH], [0.8905 ± 0.0048], [0.8898 ± 0.0053],
  )),
  caption: [Unakrsna validacija: strukturna PH ne pomaže povrh tf-idf-a.],
)

Prosečna razlika je ponovo blago negativna ($-0.0017$), kombinovani model je bolji u samo
2 od 10 foldova, $p = 0.08$. Ukupan udeo strukturnih karakteristika u značaju šume je oko
1.8%, malo veći nego kod semantičke PH, ali i dalje nedovoljan.

== Deskriptivno poređenje klasa
Umesto klasifikacije, možemo direktno pitati: da li se tri klase uopšte topološki
razlikuju? Za svaku klasu posmatramo njen indukovani citatni podgraf (strukturna strana) i
uzorak njenog tf-idf oblaka (semantička strana).

#figure(
  rect(table(
    columns: (auto, auto, auto, auto, auto),
    table.header([*Klasa*], [*Radova*], [*Citata*], [*Pros. stepen*], [*Komponenti*]),
    [Klasa 0], [4103], [5212], [2.54], [842],
    [Klasa 1], [7739], [14563], [3.76], [678],
    [Klasa 2], [7875], [15790], [4.01], [1124],
  )),
  caption: [Strukturni profil citatnih podgrafova po klasama.],
)

Strukturno se klase razlikuju: klasa 0 je najmanja i najređe povezana. Semantički, međutim,
tri klase imaju gotovo isti oblik. Njihove $H_1$ Betti krive (broj petlji tf-idf oblaka u
zavisnosti od praga) se skoro poklapaju, sa vrhom oko praga 0.7:

#figure(
  image("images/class_betti_curves.png", width: 68%),
  caption: [Semantičke $H_1$ Betti krive tri klase, gotovo identičan topološki profil.]
)

Klase se, dakle, razlikuju po gustini citatne mreže, ali ne i po obliku u semantičkom
prostoru. Signal koji izvlačimo iz topologije (gustina povezivanja, sličnost tema) jeste stvaran, ali ga tf-idf već sadrži.

== Bogatiji feature-i, pretraga i objedinjeni model
Do sada su topološki feature-i bili šest skalara (entropija i deskriptori) po čvoru. Prirodno
je zapitati se da li bi bogatija reprezentacija ili kombinovanje pristupa promenili
zaključak. Idemo u tri pravca. (Kod celog poglavlja, uključujući ova proširenja, je u
notebooku `perzistentna_homologija_pubmed.ipynb`.)

Prvi je vektorizacija dijagrama. Umesto sažimanja u entropiju, svaki po-čvor dijagram
pretvaramo u _Persistence Image_, zaglađenu 2D sliku po koordinatama (nastanak, trajnost),
zasebno za $H_0$ i $H_1$, koju izravnamo u vektor od 50 brojeva. Ovakav mnogo bogatiji opis
lokalne topologije ipak ne pomaže: pod unakrsnom validacijom tf-idf ostaje na $0.8922$, a uz
Persistence Image pada na $0.8902$.

Drugi pravac je pretraga po definiciji okoline (1-hop naspram 2-hop) i tipu feature-a
(entropija naspram slike), petostrukom unakrsnom validacijom:

#figure(
  rect(table(
    columns: (auto, auto),
    table.header([*Konfiguracija*], [*CV tačnost*]),
    [tf-idf (baseline)], [*0.8934*],
    [1-hop entropija (6)], [0.8908],
    [2-hop entropija (6)], [0.8907],
    [1-hop slika (50)], [0.8901],
    [2-hop slika (50)], [0.8889],
  )),
  caption: [Pretraga po okolini i vektorizaciji: nijedna varijanta ne prelazi baseline.],
)

Nijedna konfiguracija ne prevazilazi čist tf-idf. Ni više hopova ni bogatija slika ne
otključavaju nov signal.

Treći pokušaj je objedinjeni model: tf-idf plus sve topološke reprezentacije
zajedno (semantička entropija, strukturna PH i Persistence Image), ukupno 62 dodatne kolone.
Ovaj model je najlošiji od svih: tačnost pada sa $0.8922$ na $0.8868$.
Dodavanjem mnoštva slabo-informativnih, međusobno redundantnih kolona uz 500-dimenzioni
tf-idf samo otežavamo slučajnoj šumi da napravi dobre podele.

Ni bogatija vektorizacija ni objedinjeni model, dakle, ne menjaju zaključak: povrh tf-idf-a
nijedan od isprobanih topoloških pristupa ne donosi robusno poboljšanje. Razlog je to što
radovi obično citiraju druge radove iz iste oblasti, pa njihova povezanost citatima i raspored
u prostoru reči govore uglavnom o temi rada, a tu informaciju tf-idf vektor već sadrži.
Topološke karakteristike zato ne daju ništa novo, samo istu informaciju u drugom obliku.

= Zaključak
Prošli smo kroz dve najčešće metode topološke analize podataka, perzistentnu homologiju i
mapper. Na jednostavnim, čisto geometrijskim primerima (kružnica, sfera, torus) perzistentna
homologija bez greške razlikuje oblike, jer tamo topološka struktura zaista postoji i nosi svu
informaciju. Na stvarnom skupu poput PubMed-a slika je drugačija: nijedna od metoda nije nadmašila običan tf-idf, ni mapper ni perzistentna homologija. Razlog
nije u tome što su metode loše, već što u ovim podacima ne dobijamo ništa što tf-idf već ne zna.

Glavna pouka je da TDA ne pomaže svakom klasifikatoru sam po sebi. Isplati se tek kada u podacima postoji topološka struktura koju jednostavnije reprezentacije ne hvataju.
Kada takve strukture nema, dodatni topološki feature-i samo unose šum.

Ipak, to ne znači da oblast nema budućnost. Topološka analiza podataka je još uvek mlada i ima
visok prag ulaska jer traži solidne osnove algebarske topologije, pa se delom zato razvija
sporije od drugih modernih pristupa. Za sada se isplati koristiti je ciljano, tamo gde struktura
podataka nije očigledna, a ne kao podrazumevani dodatak svakom modelu.
