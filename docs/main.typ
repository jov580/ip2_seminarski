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

= Zaključak
Topološka analiza podataka je suštinski mlada oblast (počinje oko 2007. godine) i 
vremenom će postajati bolja. S obzirom i na to da je sam prvi stepenik upuštanja 
u oblast visok (osnove algebarske topologije zahtevaju i mnoge napredne koncepte
"jednostavnijih" podoblasti topologije kao vešto baratanje algebrom), razvija se 
relativno sporo u odnosu na druge moderne pristupe. Jedno mesto za koje se trenutno
bori jesu novi slojevi u neuronskim mrežama. Tu nailaze na problem računske složenosti
zbog kojih često bivaju preskočeni. Međutim, ko zna. I transformer je bolno spor 
ali je trenutno kičma modernih neuronskih mreža u praktično svim oblastima!
