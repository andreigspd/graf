#include <iostream>
#include <fstream>
#include <graphics.h>
#include <winbgim.h>
#include <stdio.h>
#include <math.h>
#include <queue>
#include <stack>

#define PI 3.14159265
using namespace std;
enum stareAplicatie {
    NEUTRU,
    ADAUGA_NOD,
    ADAUGA_MUCHIE_1,
    ADAUGA_MUCHIE_2,
    SETEAZA_COST_1,
    SETEAZA_COST_2,
    MUTARE_NOD,
    STERGE_NOD,
    STERGE_MUCHIE_1,
    SALVARE_GRAF,
    LOAD_GRAF,
    START_DFS,
    START_BFS,
    ARANJARE_CERC,
    ROY_FLOYD,
    DIJKSTRA,
    PRIM,
    KRUSKAL,
    HIGHLIGHT_CC,
    HIGHLIGHT_TC,
    PUNCTE_ARTICULATIE,
	BIPARTIT
};

struct nod {
    int x, y;//coordonatele fiecarui nod
    int info;//retine informatia din nod
    int viz;//0-alb(nevizitat), 1-verde(vizitat),2-rosu(curent)
}Noduri[301];

struct muchie {
    int nod1, nod2;
    int cost;//pt grafuri cu costuri
    int culoare;//0-normala, 1-rosie(dijsktra)
}Muchie[301];

int n, m, mat[301][301];//n=nr noduri, m=nr muchii, mat - mat de adiacenta
int pagina = 0;//pt buffering, modificarile scenei se fac pe pagina din spate, si se
//actualizeaza pe pagina vizibila abia dupa
int razaNod = 20;
stareAplicatie stareCurenta = NEUTRU;
int nodStart = 0;//pt adaugare muchii
int nodMutat = 0;//pt mutare
int screenWidth, screenHeight;
int esteOrientat = 0;
int latimeButon = 250;
int inaltimeButon = 40;
char mesajEroare[200] = "";
int distDJK[101];//dist dijkstra
int distPrim[101];//dist prim
int d[101][101];//mat royfloyd
int tata[101];//vector tata
int costTotalPrim = -1;
int costTotalKruskal = -1;
int culoareNodCC[101];
int culoareNodBipartit[101];
bool eBipartit;
int matBipartit[101][101];
stack <int> stackTC;
int matTC[101][101];
#define INF 1e9

int timpDescoperire[301];//pt comp biconexe
int lowLink[301];
int parinteArt[301];
int counterArt;


int getNodPentruClick(int x, int y) {//pentru a ne da seama de muchii
    for (int i = 1; i <= n; i++) {
        double dist = sqrt(pow(x - Noduri[i].x, 2) + pow(y - Noduri[i].y, 2));
        if (dist <= razaNod)return i;
    }
    return 0;
}
int getMuchiePentruClick(int n1, int n2) {//index muchie care uneste doua noduri, daca exista
    for (int i = 1; i <= m; i++) {
        if (Muchie[i].nod1 == n1 && Muchie[i].nod2 == n2)return i;
        if (esteOrientat == 0 && Muchie[i].nod1 == n2 && Muchie[i].nod2 == n1)return i;
    }
    return -1;
}
int estePozitieNodValida(int x, int y, int nodIgnorat) {//pentru amplasare noduri, sa nu fie prea aproape unul de celalalt
    for (int i = 1; i <= n; i++) {
        if (i == nodIgnorat)continue;
        double dist = sqrt(pow(x - Noduri[i].x, 2) + pow(y - Noduri[i].y, 2));
        if (dist < 2 * razaNod + 10)return 0;
    }
    return 1;
}
void getPozitieLegala(int xMouse, int yMouse, int& xFinal, int& yFinal) {//atunci cand mutam un nod inafara blackboxului
    int limitaStanga = latimeButon + 20 + razaNod;
    int limitaDreapta = screenWidth - latimeButon - 20 - razaNod;
    int limitaSus = razaNod + 10;
    int limitaJos = screenHeight - razaNod + 30;

    if (xMouse < limitaStanga)xFinal = limitaStanga;
    else if (xMouse > limitaDreapta)xFinal = limitaDreapta;
    else xFinal = xMouse;

    if (yMouse > limitaJos)yFinal = limitaJos;
    else if (yMouse < limitaSus)yFinal = limitaSus;
    else yFinal = yMouse;
}
void stergeMuchieLogica(int n1, int n2) {
    mat[n1][n2] = 0;
    if (!esteOrientat)mat[n2][n1] = 0;
    int idx = getMuchiePentruClick(n1, n2);
    if (idx != -1) {
        Muchie[idx] = Muchie[m];
        m--;
    }
}
void stergeNodLogica(int k) {
    //la stergere nod e mai complicat, trb modificate mai multe chestii
    int mNou = 0;
    for (int i = 1; i <= m; i++) {
        if (Muchie[i].nod1 == k || Muchie[i].nod2 == k)continue;//se sterge muchia care contine nodul k
        if (Muchie[i].nod1 > k)Muchie[i].nod1--;//si se decrementeaza indexii celorlalte noduri
        if (Muchie[i].nod2 > k)Muchie[i].nod2--;
        Muchie[++mNou] = Muchie[i];
    }
    m = mNou;
    for (int i = k; i < n; i++) {
        Noduri[i] = Noduri[i + 1];//se stereg nodul k
    }
    for (int i = 1; i < n; i++) {
        Noduri[i].info = i;// se actualizeaza indexii
    }
    for (int i = k; i < n; i++) {
        for (int j = 1; j <= n; j++) {
            mat[i][j] = mat[i + 1][j];//se sterge linia k din mat adiac
        }
    }
    for (int i = k; i < n; i++) {
        for (int j = 1; j <= n; j++) {
            mat[i][j] = mat[i][j + 1];//la fel si coloana k
        }
    }
    for (int i = 1; i <= n; i++) {
        mat[n][i] = 0;//elem de pe ultima linie se sterg
        mat[i][n] = 0;//si pe ult coloana
    }
    n--;//nr noduri --
}

void deseneazaButon(int x, int y, char* text, bool esteActiv) {
    if (esteActiv) {
        setfillstyle(SOLID_FILL, GREEN);//daca e selectat butonul se face verde
    }
    else setfillstyle(SOLID_FILL, LIGHTGRAY);// daca nu ramane gri
    bar(x, y, x + latimeButon, y + inaltimeButon);//inauntrul butonului
    setcolor(BLUE);
    rectangle(x, y, x + latimeButon, y + inaltimeButon);//conturul butonului
    setbkcolor(esteActiv ? GREEN : LIGHTGRAY);
    settextstyle(DEFAULT_FONT, HORIZ_DIR, 2);
    int xText = x + latimeButon / 2 - textwidth(text) / 2;//pt centrare text in mijloc
    int yText = y + inaltimeButon / 2 - textheight(text) / 2;

    outtextxy(xText, yText, text);
}
void deseneazaStart() {
    setactivepage(1 - pagina);
    setbkcolor(BLACK);
    cleardevice();
    setfillstyle(SOLID_FILL, DARKGRAY);
    bar(0, 0, screenWidth, screenHeight);
    setcolor(RED);
    settextstyle(DEFAULT_FONT, HORIZ_DIR, 4);
    char text[] = "Algoritmica Grafurilor";
    setbkcolor(DARKGRAY);
    outtextxy(screenWidth / 2 - textwidth(text) / 2, 100, text);

    int midX = screenWidth / 2 - latimeButon / 2;
    int midY = screenHeight / 2;

    deseneazaButon(midX, midY - 60, "Graf orientat", false);
    deseneazaButon(midX, midY, "Graf neorientat", false);
	deseneazaButon(midX, midY + 60, "Informatii", false);
    deseneazaButon(midX, midY + 120, "Iesire", false);

    setvisualpage(1 - pagina);
    pagina = 1 - pagina;
}
void deseneazaMatRF()
{
    int left = latimeButon + 30;
    int right = screenWidth - latimeButon - 30;
    int top = 80;
    int bottom = screenHeight - 140;

    setfillstyle(SOLID_FILL, BLACK);
    bar(left - 10, top - 10, right + 10, bottom + 10); // curata zona

    setcolor(YELLOW);
    setbkcolor(BLACK);
    settextstyle(DEFAULT_FONT, HORIZ_DIR, 2);
    if (n <= 0) {
        outtextxy(left, top, "Nu exista noduri pentru matrice.");
        return;
    }
    int availW = right - left;
    int availH = bottom - top;
    int cellW = availW / (n + 1);
    int cellH = availH / (n + 1);
    int cellSize = min(cellW, cellH);
    if (cellSize < 24)//daca e prea mica celula, schimbam fontul
    {
        settextstyle(SMALL_FONT, HORIZ_DIR, 2);
        if (cellSize < 12)
            cellSize = 12;
    }
    else
    {
        settextstyle(DEFAULT_FONT, HORIZ_DIR, 2);
    }
    // desenam etichetele coloanelor
    int startX = left;
    int startY = top;
    for (int j = 1; j <= n; j++) {
        char buf[32];
        sprintf(buf, "%d", j);
        int x = startX + j * cellSize + cellSize / 2 - textwidth(buf) / 2;
        int y = startY;
        setcolor(WHITE);
        outtextxy(x, y, buf);
    }
    // desenam etichetele randurilor si valorile
    for (int i = 1; i <= n; i++) {
        char bufRow[32];
        sprintf(bufRow, "%d", i);
        int y = startY + i * cellSize + cellSize / 2 - textheight(bufRow) / 2;
        int xLabel = startX;
        setcolor(WHITE);
        outtextxy(xLabel, y, bufRow);

        for (int j = 1; j <= n; j++) {
            int xCell = startX + j * cellSize;
            int yCell = startY + i * cellSize;

            char txt[32];
            if (d[i][j] == INF)
            {
                setcolor(RED);
                sprintf(txt, "INF");
            }
            else
            {
                setcolor(MAGENTA);
                sprintf(txt, "%d", d[i][j]);
            }

            int tx = xCell + cellSize / 2 - textwidth(txt) / 2;
            int ty = yCell + cellSize / 2 - textheight(txt) / 2;
            outtextxy(tx, ty, txt);

            setcolor(DARKGRAY);
            rectangle(xCell, yCell, xCell + cellSize, yCell + cellSize);
        }
    }
}
void deseneazaScena() {
    setactivepage(1 - pagina);
    setbkcolor(BLACK); //pt a nu ramane bkg rosu sau verde dupa un dfs
    cleardevice();
    //
    settextstyle(DEFAULT_FONT, HORIZ_DIR, 3);
    setfillstyle(SOLID_FILL, DARKGRAY);
    bar(0, 0, latimeButon + 20, screenHeight);
    bar(screenWidth - latimeButon - 20, 0, screenWidth, screenHeight);
    //titlu meniuri
    int xText = 10 + latimeButon / 2 - textwidth("Format Graf") / 2;
    int yText = inaltimeButon + 10 + inaltimeButon / 2 - textheight("Format Graf") / 2;
    setbkcolor(DARKGRAY);
    setcolor(BLACK);
    outtextxy(xText, yText, "Format Graf");
    xText = screenWidth - (10 + latimeButon / 2 + textwidth("Algoritmi") / 2);
    yText = inaltimeButon + 10 + inaltimeButon / 2 - textheight("Algoritmi") / 2;
    setbkcolor(DARKGRAY);
    setcolor(BLACK);
    outtextxy(xText, yText, "Algoritmi");
    //butoane desenare
    deseneazaButon(10, 2 * (inaltimeButon + 10), "Adauga Nod", (stareCurenta == ADAUGA_NOD));
    deseneazaButon(10, 3 * (inaltimeButon + 10), "Adauga Muchie", (stareCurenta == ADAUGA_MUCHIE_1));
    deseneazaButon(10, 4 * (inaltimeButon + 10), "Adauga Cost", (stareCurenta == SETEAZA_COST_1));
    deseneazaButon(10, 5 * (inaltimeButon + 10), "Aranjare Cerc", (stareCurenta == ARANJARE_CERC));
    deseneazaButon(10, 6 * (inaltimeButon + 10), "Muta Nod", (stareCurenta == MUTARE_NOD));
    deseneazaButon(10, 7 * (inaltimeButon + 10), "Sterge Nod", (stareCurenta == STERGE_NOD));
    deseneazaButon(10, 8 * (inaltimeButon + 10), "Sterge Muchie", (stareCurenta == STERGE_MUCHIE_1));
    deseneazaButon(10, 9 * (inaltimeButon + 10), "Salveaza Graf", (stareCurenta == SALVARE_GRAF));
    deseneazaButon(10, 10 * (inaltimeButon + 10), "Incarca Graf", (stareCurenta == LOAD_GRAF));

    deseneazaButon(screenWidth - 15 - latimeButon, 2 * (inaltimeButon + 10), "Start DFS", (stareCurenta == START_DFS));
    deseneazaButon(screenWidth - 15 - latimeButon, 3 * (inaltimeButon + 10), "Start BFS", (stareCurenta == START_BFS));
    deseneazaButon(screenWidth - 15 - latimeButon, 4 * (inaltimeButon + 10), "Arata Mat RF", (stareCurenta == ROY_FLOYD));
    deseneazaButon(screenWidth - 15 - latimeButon, 5 * (inaltimeButon + 10), "Dijkstra", (stareCurenta == DIJKSTRA));
    deseneazaButon(screenWidth - 15 - latimeButon, 6 * (inaltimeButon + 10), "Check bipartit", (stareCurenta == BIPARTIT));
    if (!esteOrientat)
    {
        deseneazaButon(screenWidth - 15 - latimeButon, 7 * (inaltimeButon + 10), "Prim", (stareCurenta == PRIM));
        deseneazaButon(screenWidth - 15 - latimeButon, 8 * (inaltimeButon + 10), "Kruskal", (stareCurenta == KRUSKAL));
        deseneazaButon(screenWidth - 15 - latimeButon, 9 * (inaltimeButon + 10), "Highlight CC", (stareCurenta == HIGHLIGHT_CC));
        deseneazaButon(screenWidth - 15 - latimeButon, 10 * (inaltimeButon + 10), "HL Pct. Artic.", (stareCurenta == PUNCTE_ARTICULATIE));

    }
    else {//pt grafuri orientate
        deseneazaButon(screenWidth - 15 - latimeButon, 7 * (inaltimeButon + 10), "Highlight TC", (stareCurenta == HIGHLIGHT_TC));
    }
    deseneazaButon(10, screenHeight - 150, "Reset", false);
    deseneazaButon(10, screenHeight - 100, "Iesire", false);
    deseneazaButon(screenWidth - latimeButon - 15, screenHeight - 100, "Inapoi", false);

    if (stareCurenta == ROY_FLOYD)
    {
        deseneazaMatRF();
        setvisualpage(1 - pagina);
        pagina = 1 - pagina;
        return;
    }

    //muchii desenare
    setlinestyle(SOLID_LINE, HORIZ_DIR, 3);
    for (int i = 1; i <= m; i++) {
        setcolor(CYAN);
        if (Muchie[i].culoare == 1)setcolor(RED);
        setlinestyle(SOLID_LINE, 0, 4);
        int x1 = Noduri[Muchie[i].nod1].x;
        int y1 = Noduri[Muchie[i].nod1].y;
        int x2 = Noduri[Muchie[i].nod2].x;
        int y2 = Noduri[Muchie[i].nod2].y;
        if (esteOrientat == 0) {//linie simpla
            line(x1, y1, x2, y2);
        }
        else {//pt grafuri orientate linie cu sagata
            double angle = atan2(y2 - y1, x2 - x1);//unghiul dreptei dintre centrele nodurilor
            int xStop = x2 - razaNod * cos(angle);// x pe cerc = RcosTHETA
            int yStop = y2 - razaNod * sin(angle);//y pe cerc = RsinTHETA

            line(x1, y1, xStop, yStop);
            double lungimeSageata = 15; //lungimea sagetii
            double unghiSageata = 0.5; //orienarea ei (in radiani) ~30 grade

            int aripa1x = xStop - lungimeSageata * cos(angle - unghiSageata);
            int aripa1y = yStop - lungimeSageata * sin(angle - unghiSageata);
            line(xStop, yStop, aripa1x, aripa1y);

            int aripa2x = xStop - lungimeSageata * cos(angle + unghiSageata);
            int aripa2y = yStop - lungimeSageata * sin(angle + unghiSageata);
            line(xStop, yStop, aripa2x, aripa2y);
        }
        if (Muchie[i].cost > 1) {
            char costMuchie[16] = "";
            sprintf(costMuchie, "%d", Muchie[i].cost);
            setcolor(MAGENTA);
            setbkcolor(BLACK);
            settextstyle(SMALL_FONT, HORIZ_DIR, 8);
            int midX = (x1 + x2) / 2;
            int midY = (y1 + y2) / 2;
            //outtextxy(midX, midY, costMuchie);
            if (esteOrientat) {
                double angle = atan2(y2 - y1, x2 - x1);//unghiul dreptei dintre noduri
                //ca sa pot pozitiona costul in functie de directie
                midX = midX + 15 * cos(angle + PI / 2);//angle + pi/2 o sa mute textul in dreapta directiei de mers
                midY = midY + 15 * sin(angle + PI / 2);
            }
            outtextxy(midX - textwidth(costMuchie) / 2, midY - textheight(costMuchie) / 2, costMuchie);
        }

    }
    if (stareCurenta == ADAUGA_MUCHIE_2) {//desenare muchie in timp real
        int x1 = Noduri[nodStart].x;
        int y1 = Noduri[nodStart].y;
        int x2 = mousex();
        int y2 = mousey();
        setcolor(CYAN);
        if (esteOrientat == 0) {//linie simpla
            line(x1, y1, x2, y2);
        }
        else {//pt grafuri orientate linie cu sagata
            double angle = atan2(y2 - y1, x2 - x1);//unghiul dreptei dintre centrele nodurilor
            int xStop = x2 - razaNod * cos(angle);// x pe cerc = RcosTHETA
            int yStop = y2 - razaNod * sin(angle);//y pe cerc = RsinTHETA

            line(x1, y1, xStop, yStop);
            double lungimeSageata = 15; //lungimea sagetii
            double unghiSageata = 0.5; //orienarea ei (in radiani) ~30 grade

            int aripa1x = xStop - lungimeSageata * cos(angle - unghiSageata);
            int aripa1y = yStop - lungimeSageata * sin(angle - unghiSageata);
            line(xStop, yStop, aripa1x, aripa1y);

            int aripa2x = xStop - lungimeSageata * cos(angle + unghiSageata);
            int aripa2y = yStop - lungimeSageata * sin(angle + unghiSageata);
            line(xStop, yStop, aripa2x, aripa2y);
        }
    }
    //noduri desenare

    settextstyle(DEFAULT_FONT, HORIZ_DIR, 2);
    for (int i = 1; i <= n; i++) {
        int xPixel = Noduri[i].x;
        int yPixel = Noduri[i].y;
        setcolor(WHITE);
        if (Noduri[i].viz == 0) { setfillstyle(SOLID_FILL, BLACK); setbkcolor(BLACK); } //nevizitat
        if (Noduri[i].viz == 1) { setfillstyle(SOLID_FILL, GREEN); setbkcolor(GREEN); } //vizitat
        if (Noduri[i].viz == 2) { setfillstyle(SOLID_FILL, RED); setbkcolor(RED); }     //curent
        if (Noduri[i].viz == 3) { setfillstyle(SOLID_FILL, YELLOW); setbkcolor(YELLOW); setcolor(BLACK); }//in coada bfs
        if (Noduri[i].viz == 4) { setfillstyle(SOLID_FILL, LIGHTRED); setbkcolor(LIGHTRED); setcolor(WHITE); }//pct art.

        if (stareCurenta == BIPARTIT)
        {
            if (culoareNodBipartit[i] == 1)
            {
                setfillstyle(SOLID_FILL, GREEN);
				setbkcolor(GREEN);
            }
			else if (culoareNodBipartit[i] == 0)
            {
				setfillstyle(SOLID_FILL, RED);
				setbkcolor(RED);
            }
            else if(culoareNodBipartit[i]==-1)
            {
                setfillstyle(SOLID_FILL, BLACK);
                setbkcolor(BLACK);
            }
        }
        if (stareCurenta == HIGHLIGHT_CC || stareCurenta == HIGHLIGHT_TC)
        {
            switch (culoareNodCC[i])
            {
            case 1:
                setfillstyle(SOLID_FILL, BLUE);
                setbkcolor(BLUE);
                break;
            case 2:
                setfillstyle(SOLID_FILL, GREEN);
                setbkcolor(GREEN);
                break;
            case 3:
                setfillstyle(SOLID_FILL, CYAN);
                setbkcolor(CYAN);
                break;
            case 4:
                setfillstyle(SOLID_FILL, RED);
                setbkcolor(RED);
                break;
            case 5:
                setfillstyle(SOLID_FILL, MAGENTA);
                setbkcolor(MAGENTA);
                break;
            case 6:
                setfillstyle(SOLID_FILL, BROWN);
                setbkcolor(BROWN);
                break;
            case 9:
                setfillstyle(SOLID_FILL, LIGHTBLUE);
                setbkcolor(LIGHTBLUE);
                break;
            case 10:
                setfillstyle(SOLID_FILL, LIGHTGREEN);
                setbkcolor(LIGHTGREEN);
                break;
            case 11:
                setfillstyle(SOLID_FILL, LIGHTCYAN);
                setbkcolor(LIGHTCYAN);
                break;
            case 12:
                setfillstyle(SOLID_FILL, LIGHTRED);
                setbkcolor(LIGHTRED);
                break;
            case 13:
                setfillstyle(SOLID_FILL, LIGHTMAGENTA);
                setbkcolor(LIGHTMAGENTA);
                break;
            case 14:
                setfillstyle(SOLID_FILL, YELLOW);
                setbkcolor(YELLOW);
                break;
            default:
                break;
            }
        }

        if (i == nodMutat) {
            setfillstyle(SOLID_FILL, LIGHTRED);
            setbkcolor(LIGHTRED);
        }
        fillellipse(xPixel, yPixel, razaNod, razaNod);
        if (stareCurenta == DIJKSTRA) {//pt dijsktra afisez distantele deasupra nodurilor
            char distanta[20] = "";
            if (distDJK[i] != INF)sprintf(distanta, "%d", distDJK[i]);
            else strcpy(distanta, "INF");
            setcolor(YELLOW);
            setbkcolor(BLACK);
            outtextxy(xPixel - textwidth(distanta) / 2, yPixel - razaNod - 15, distanta);
        }

        char text[10] = "";
        sprintf(text, "%d", Noduri[i].info); //nr nodului il punem in sir de caractere

        int xText = xPixel - textwidth(text) / 2;
        int yText = yPixel - textheight(text) / 2;
        outtextxy(xText, yText, text);//il afisam in centrul cercului
    }

    if (strlen(mesajEroare) > 0) {//text rosu de eroare
        setcolor(RED);
        setbkcolor(BLACK);
        settextstyle(BOLD_FONT, HORIZ_DIR, 2);
        outtextxy(latimeButon + 30, screenHeight - 50, mesajEroare);
    }
    else {
        char mesaj[200] = ""; //text cu galben in colt ecran, zice ce sa facem
        if (stareCurenta == NEUTRU) {
            strcpy(mesaj, "Selecteaza o optiune din meniu");
        }
        else if (stareCurenta == ADAUGA_NOD) {
            strcpy(mesaj, "Da click pe zona neagra");
        }
        else if (stareCurenta == ADAUGA_MUCHIE_1) {
            strcpy(mesaj, "Selecteaza primul nod");
        }
        else if (stareCurenta == ADAUGA_MUCHIE_2) {
            strcpy(mesaj, "Selecteaza al doilea nod");
        }
        else if (stareCurenta == SETEAZA_COST_1) {
            strcpy(mesaj, "Selecteaza primul nod");
        }
        else if (stareCurenta == SETEAZA_COST_2) {
            strcpy(mesaj, "Selecteaza al doilea nod");

        }
        else if (stareCurenta == MUTARE_NOD) {
            strcpy(mesaj, "Selecteaza nod de mutat");
        }
        else if (stareCurenta == STERGE_NOD) {
            strcpy(mesaj, "Selecteaza nod pentru stergere");
        }
        else if (stareCurenta == STERGE_MUCHIE_1) {
            strcpy(mesaj, "Selecteaza noduri pentru stergere muchii");
        }
        else if (stareCurenta == START_DFS) {
            strcpy(mesaj, "Selecteaza nod de start");
        }
        else if (stareCurenta == START_BFS) {
            strcpy(mesaj, "Selecteaza nod de start");
        }
        else if (stareCurenta == BIPARTIT) {
            strcpy(mesaj, "Selecteaza nod de start");
        }
        setcolor(YELLOW);
        setbkcolor(BLACK);
        outtextxy(latimeButon + 30, screenHeight - 50, mesaj);
    }
    if (costTotalPrim != -1) {
        char textScor[50];
        sprintf(textScor, "Cost Total APM Prim: %d", costTotalPrim);

        setcolor(YELLOW);
        setbkcolor(BLACK);
        settextstyle(DEFAULT_FONT, HORIZ_DIR, 3);
        outtextxy(screenWidth / 2 - textwidth(textScor) / 2, 30, textScor);
    }
    if (costTotalKruskal != -1) {
        char textScor[50];
        sprintf(textScor, "Cost Total APM Kruskal: %d", costTotalKruskal);
        setcolor(YELLOW);
        setbkcolor(BLACK);
        settextstyle(DEFAULT_FONT, HORIZ_DIR, 3);
        outtextxy(screenWidth / 2 - textwidth(textScor) / 2, 30, textScor);
    }

    setvisualpage(1 - pagina);
    pagina = 1 - pagina;//schimbam pagina
}
void dfs(int start)
{
    Noduri[start].viz = 2;
    deseneazaScena(); //desenam dupa fiecare nod
    delay(500);
    for (int j = 1; j <= n; j++)
    {
        if (mat[start][j] >= 1 && Noduri[j].viz == 0) {
            Noduri[start].viz = 1;
            dfs(j);
        }
    }
    Noduri[start].viz = 1; //nod curent il facem nod vizitat

}
void bfs(int start)
{
    int nodCurr;
    queue<int> q;
    q.push(start);
    Noduri[start].viz = 3;
    deseneazaScena();
    delay(500);
    while (!q.empty())
    {
        nodCurr = q.front();
        q.pop();
        Noduri[nodCurr].viz = 2;
        deseneazaScena();
        delay(500);
        for (int i = 1; i <= n; i++)
        {
            if (mat[nodCurr][i] != 0 && Noduri[i].viz == 0)
            {
                Noduri[i].viz = 3;//coloreaza nodurile din coada galbene
                q.push(i);
                deseneazaScena();
                delay(500);
            }
        }
        Noduri[nodCurr].viz = 1;
        deseneazaScena();
        delay(300);
    }
}
void royFloyd()
{
    for (int i = 1; i <= n; i++)
        for (int j = 1; j <= n; j++)
            if (mat[i][j] == 0 && i != j)
                d[i][j] = INF;
            else
                d[i][j] = mat[i][j];
    for (int k = 1; k <= n; k++)
    {
        for (int i = 1; i <= n; i++)
        {
            for (int j = 1; j <= n; j++)
            {
                if (d[i][k] != INF && d[k][j] != INF && d[i][k] + d[k][j] < d[i][j])
                {
                    d[i][j] = d[i][k] + d[k][j];
                }
            }
        }
    }
}
void dijkstraAlgoritm(int start) {
    for (int i = 1; i <= m; i++)Muchie[i].culoare = 0;//resetez muchiile
    for (int i = 1; i <= n; i++) {
        tata[i] = 0;
        if (mat[start][i] != 0) {
            distDJK[i] = mat[start][i];//setez costurile de la muchia de start la vecinii ei
            tata[i] = start;// la fel si tatii
        }
        else distDJK[i] = INF;
        //v[i] = 0;//resetez si vizitat
        Noduri[i].viz = 0;
    }
    //v[start] = 1;
    Noduri[start].viz = 1;
    distDJK[start] = 0;
    tata[start] = 0;
    distDJK[0] = INF;
    for (int i = 1; i < n; i++) {
        int nodCostMin = 0;
        for (int j = 1; j <= n; j++) {
            if (Noduri[j].viz == 0 && distDJK[j] < distDJK[nodCostMin])nodCostMin = j;
        }
        if (nodCostMin == 0)break;
        if (tata[nodCostMin]) {//muchie folosita la drum minim
            int indexMuchie = getMuchiePentruClick(tata[nodCostMin], nodCostMin);
            if (indexMuchie != -1)Muchie[indexMuchie].culoare = 1;
        }
        //v[nodCostMin] = 1;
        Noduri[nodCostMin].viz = 1;
        deseneazaScena();
        delay(1000);
        for (int j = 1; j <= n; j++) {
            if (Noduri[j].viz == 0 && mat[nodCostMin][j] && distDJK[j] > distDJK[nodCostMin] + mat[nodCostMin][j]) {
                distDJK[j] = distDJK[nodCostMin] + mat[nodCostMin][j];
                tata[j] = nodCostMin;
            }
        }
    }
    //for(int i=1;i<=n;i++)cout<<distDJK[i]<<' ';
}
void PrimAlgoritm(int start) {
    costTotalPrim = 0;
    for (int i = 1; i <= m; i++)Muchie[i].culoare = 0;
    for (int i = 1; i <= n; i++) {
        distPrim[i] = INF;
        Noduri[i].viz = 0;
        tata[i] = 0;
    }
    distPrim[start] = 0;
    for (int i = 1; i <= n; i++) {
        int nodMin = 0;
        int costMin = INF;
        for (int j = 1; j <= n; j++) {
            if (Noduri[j].viz == 0 && distPrim[j] < costMin) {
                costMin = distPrim[j];
                nodMin = j;
            }
        }
        if (nodMin == 0)break;
        costTotalPrim = costTotalPrim + distPrim[nodMin];


        Noduri[nodMin].viz = 1;
        if (tata[nodMin]) {
            int indexMuchie = getMuchiePentruClick(tata[nodMin], nodMin);
            if (indexMuchie != -1)Muchie[indexMuchie].culoare = 1;
        }
        deseneazaScena();
        delay(1000);
        for (int j = 1; j <= n; j++) {
            if (Noduri[j].viz == 0 && mat[nodMin][j]) {
                if (mat[nodMin][j] < distPrim[j]) {
                    distPrim[j] = mat[nodMin][j];
                    tata[j] = nodMin;
                }
            }
        }
    }

}
void kruskalAlgoritm()
{
    muchie MuchiiK[301];
    costTotalKruskal = 0;
    for (int i = 1; i <= n; i++)
        tata[i] = i;
    for (int i = 1; i <= m; i++)
        MuchiiK[i] = Muchie[i];
    for (int i = 1; i < m; i++)
        for (int j = i + 1; j <= m; j++)
            if (MuchiiK[i].cost > MuchiiK[j].cost)
                swap(MuchiiK[i], MuchiiK[j]);
    for (int i = 1; i <= m; i++)
    {
        if (tata[MuchiiK[i].nod1] != tata[MuchiiK[i].nod2])
        {
            costTotalKruskal += MuchiiK[i].cost;
            int indexMuchie = getMuchiePentruClick(MuchiiK[i].nod1, MuchiiK[i].nod2);
            if (indexMuchie != -1)Muchie[indexMuchie].culoare = 1;
            Noduri[MuchiiK[i].nod1].viz = 1;
            Noduri[MuchiiK[i].nod2].viz = 1;
            deseneazaScena();
            delay(1000);
            int arb1 = tata[MuchiiK[i].nod1];
            int arb2 = tata[MuchiiK[i].nod2];
            for (int j = 1; j <= n; j++)
                if (tata[j] == arb2)
                    tata[j] = arb1;
        }
    }
}
bool checkRF(int xMouse, int yMouse)
{
    int rfX1 = screenWidth - 15 - latimeButon;
    int rfX2 = screenWidth - 15;
    int rfY1 = 4 * inaltimeButon + 40;
    int rfY2 = 5 * inaltimeButon + 40;
    if (stareCurenta == ROY_FLOYD)
    {
        if (!(xMouse >= rfX1 && xMouse <= rfX2 && yMouse >= rfY1 && yMouse <= rfY2))
            return 1;
    }
    return 0;
}
void resetNoduriSiMuchii()
{
    costTotalPrim = -1;
    costTotalKruskal = -1;
    for (int i = 1; i <= n; i++) {
        Noduri[i].viz = 0;//resetez vectorii
    }
    for (int i = 1; i <= m; i++) {
        Muchie[i].culoare = 0; // Resetam muchiile la albastru (CYAN)
    }
}
void dfsCC(int start, int cul)
{
    culoareNodCC[start] = cul;
    Noduri[start].viz = 1;
    for (int j = 1; j <= n; j++)
    {
        if (mat[start][j] >= 1 && Noduri[j].viz == 0) {
            dfsCC(j, cul);
        }
    }
}
void componenteConexe()
{
    //avem maxim 12 culori pt componente (din cele 16 totale excludem negru, alb, gri deschis si inchis)
    int culoareCurenta = 0;
    for (int i = 1; i <= n; i++)
        culoareNodCC[i] = 0;
    for (int i = 1; i <= n; i++)
    {
        if (Noduri[i].viz == 0)
        {
            culoareCurenta++;
            if (culoareCurenta == 7)
                culoareCurenta += 2;
            if (culoareCurenta == 15)
                culoareCurenta = 1;//reincepem culorile, desi sper sa nu fie cazul sa avem atatea componente
            dfsCC(i, culoareCurenta);
        }
    }
}
void dfsTC(int start, int cul, int round)
{
    //avem maxim 12 culori pt componente (din cele 16 totale excludem negru, alb, gri deschis si inchis)
    if (round == 1)
    {
        Noduri[start].viz = 1;
        for (int i = 1; i <= n; i++)
        {
            if (mat[start][i] >= 1 && Noduri[i].viz == 0)
            {
                dfsTC(i, 0, 1);
            }
        }
        stackTC.push(start);
    }
    if (round == 2)
    {
        Noduri[start].viz = 1;
        culoareNodCC[start] = cul;
        for (int i = 1; i <= n; i++)
        {
            if (matTC[start][i] >= 1 && Noduri[i].viz == 0)
            {
                dfsTC(i, cul, 2);
            }
        }
    }
}
void kosaraju()
{
    for (int i = 1; i <= n; i++)
        if (Noduri[i].viz == 0)
            dfsTC(i, 0, 1);
    for (int i = 1; i <= n; i++)
    {
        Noduri[i].viz = 0;//resetam si vectorul de vizitare
        for (int j = 1; j <= n; j++)
            matTC[j][i] = mat[i][j];//inversam muchiile
    }
    int culoareCurenta = 0;
    while (!stackTC.empty())
    {
        int nod = stackTC.top();
        stackTC.pop();
        if (Noduri[nod].viz == 0)
        {
            culoareCurenta++;
            if (culoareCurenta == 7)
                culoareCurenta += 2;
            if (culoareCurenta == 15)
                culoareCurenta = 1;//reincepem culorile, desi sper sa nu fie cazul sa avem atatea componente
            dfsTC(nod, culoareCurenta, 2);
        }
    }
}
void saveGraf() {
    ofstream fout("graf.txt");
    fout << esteOrientat << '\n';
    fout << n << '\n';
    for (int i = 1; i <= n; i++) {
        fout << Noduri[i].x << ' ' << Noduri[i].y << '\n';
    }
    fout << m << '\n';
    for (int i = 1; i <= m; i++) {
        fout << Muchie[i].nod1 << " " << Muchie[i].nod2 << " " << Muchie[i].cost << "\n";
    }
    fout.close();
    setactivepage(getvisualpage()); // desenam pe pagina vizibila
    setcolor(GREEN);
    settextstyle(BOLD_FONT, HORIZ_DIR, 3);
    outtextxy(screenWidth / 2 - 100, screenHeight / 2, "GRAF SALVAT!");
    delay(1000); // Stam 1 secunda sa vada mesajul
}
void loadGraf() {
    ifstream fin("graf.txt");
    if (!fin.is_open()) {
        setactivepage(getvisualpage());
        setcolor(RED);
        outtextxy(screenWidth / 2 - 150, screenHeight / 2, "NU EXISTA FISIERUL!");
        delay(1000);
        return;
    }
    n = 0; m = 0;
    for (int i = 0; i < 301; i++) {
        for (int j = 0; j < 301; j++)mat[i][j] = 0;
        Noduri[i].viz = 0;
        Muchie[i].culoare = 0;
    }
    costTotalPrim = -1;
    costTotalKruskal = -1;

    fin >> esteOrientat;
    fin >> n;
    for (int i = 1; i <= n; i++) {
        fin >> Noduri[i].x >> Noduri[i].y;
        Noduri[i].viz = 0;
        Noduri[i].info = i;
    }
    fin >> m;
    for (int i = 1; i <= m; i++) {
        fin >> Muchie[i].nod1 >> Muchie[i].nod2 >> Muchie[i].cost;
        Muchie[i].culoare = 0;
        int n1 = Muchie[i].nod1;
        int n2 = Muchie[i].nod2;
        int cost = Muchie[i].cost;
        mat[n1][n2] = cost;
        if (esteOrientat == 0) {
            mat[n2][n1] = cost;
        }
    }
    fin.close();
    setactivepage(getvisualpage());
    setcolor(GREEN);
    settextstyle(BOLD_FONT, HORIZ_DIR, 3);
    outtextxy(screenWidth / 2 - 100, screenHeight / 2, "GRAF INCARCAT!");
    delay(1000);
}
void dfsArticulatie(int nod) {
    int copii = 0;
    Noduri[nod].viz = 1;
    timpDescoperire[nod] = lowLink[nod] = ++counterArt;
    for (int fiu = 1; fiu <= n; fiu++) {
        if (mat[nod][fiu]) {
            if (fiu == parinteArt[nod])continue;
            if (Noduri[fiu].viz) {
                lowLink[nod] = min(lowLink[nod], timpDescoperire[fiu]);
            }
            else {
                parinteArt[fiu] = nod;
                copii++;
                dfsArticulatie(fiu);
                lowLink[nod] = min(lowLink[nod], lowLink[fiu]);
                if (parinteArt[nod] != 0 && lowLink[fiu] >= timpDescoperire[nod]) {
                    Noduri[nod].viz = 4;
                }
            }
        }
    }
    if (parinteArt[nod] == 0 && copii > 1) {
        Noduri[nod].viz = 4; // 4 = COD CULOARE PORTOCALIU
    }
}
void findPuncteArt() {
    counterArt = 0;
    for (int i = 1; i <= n; i++) {
        Noduri[i].viz = 0;
        parinteArt[i] = 0;
        timpDescoperire[i] = 0;
        lowLink[i] = 0;
    }
    for (int i = 1; i <= n; i++) {
        if (Noduri[i].viz == 0)
            dfsArticulatie(i);
    }
    deseneazaScena();
}
void dfsBipartit(int start, bool culoare)
{
    Noduri[start].viz = 1;
    deseneazaScena();
    delay(500);
    for (int j = 1; j <= n && eBipartit; j++)
    {
        if (matBipartit[start][j] >= 1)
        {
            if (Noduri[j].viz == 0)
            {
                culoareNodBipartit[j] = 1 - culoare;
                dfsBipartit(j, 1 - culoare);
            }
            else if(culoareNodBipartit[start] == culoareNodBipartit[j])
            {
				eBipartit = false;
			}
        }
    }
}
bool handleClick(int xMouse, int yMouse, bool& apasatButonInapoi)
{
    int H = inaltimeButon + 10;
    int xDR = screenWidth - 15 - latimeButon;
    if (xMouse > latimeButon + razaNod + 20 && xMouse < screenWidth - latimeButon - razaNod - 20 || (stareCurenta == MUTARE_NOD && nodMutat != 0)) { //in afara meniului
        int nodClick = getNodPentruClick(xMouse, yMouse);
        switch (stareCurenta)
        {
        case ADAUGA_NOD:
            if (estePozitieNodValida(xMouse, yMouse, nodMutat)) {
                strcpy(mesajEroare, "");
                n++;
                Noduri[n].x = xMouse;
                Noduri[n].y = yMouse;
                Noduri[n].info = n;//se adauga nod
                costTotalPrim = -1;
            }
            else {
                strcpy(mesajEroare, "Pozitie incorecta. Da click pe ecran din nou");
                Beep(300, 300);
            }
            break;
        case ADAUGA_MUCHIE_1:
            if (nodClick != 0) {
                strcpy(mesajEroare, "");
                nodStart = nodClick; //retin primul nod
                stareCurenta = ADAUGA_MUCHIE_2;//trec in urmatoarea staer
                Noduri[nodStart].viz = 1;//ca sa il colorez
                costTotalPrim = -1;
            }
            break;
        case ADAUGA_MUCHIE_2:
            if (nodClick != 0 && nodClick != nodStart) { //ca sa fie valid
                m++;
                strcpy(mesajEroare, "");
                Muchie[m].nod1 = nodStart;
                Muchie[m].nod2 = nodClick;
                Muchie[m].cost = 1;
                mat[nodStart][nodClick] = 1;
                if (esteOrientat == 0)mat[nodClick][nodStart] = 1;
                stareCurenta = ADAUGA_MUCHIE_1;
                nodStart = 0;
            }
            else if (nodClick == nodStart) {
                strcpy(mesajEroare, "Nod selectat gresit. Alege alt nod");
                Beep(300, 300);
            }
            break;
        case SETEAZA_COST_1:
            if (nodClick != 0) {
                strcpy(mesajEroare, "");
                nodStart = nodClick;
                stareCurenta = SETEAZA_COST_2;
                Noduri[nodStart].viz = 1;
                costTotalPrim = -1;
            }
            else {
                strcpy(mesajEroare, "Selecteaza un nod valid");
                Beep(300, 600);
            }
            break;
        case SETEAZA_COST_2:
            if (nodClick != 0 && nodStart != nodClick) {
                strcpy(mesajEroare, "");
                deseneazaScena();//aici desenez scena iar inainte sa intru la citirea numarului, ca sa se salveze modificarile facute pana la momentul asta
                //cand incepe citirea se da freeze la program, si se asteapta tasta ENTER
                setactivepage(getvisualpage());
                setcolor(YELLOW);
                setbkcolor(BLACK);
                outtextxy(latimeButon + 30, screenHeight - 100, "Scrie costul si apasa ENTER:");
                char numarCitit[10] = "";
                int tastaApasata = 0;
                int lungimeNr = 0;
                while (tastaApasata != 13) { //13 este ENTER
                    if (kbhit()) {//daca e apasata tastatura
                        tastaApasata = getch();//citeste tasta apasata
                        if (tastaApasata >= '0' && tastaApasata <= '9' && lungimeNr < 5) {
                            numarCitit[lungimeNr++] = tastaApasata;
                            numarCitit[lungimeNr] = '\0';
                        }
                        else if (tastaApasata == 8 && lungimeNr > 0) {//daca e backspace se sterge ultima cifra
                            numarCitit[--lungimeNr] = '\0';
                        }

                        setfillstyle(SOLID_FILL, BLACK);//vreau ca la fiecare tasta citita sa rescriu numarul de fiecare data
                        //ca sa fie fluida citirea, deci desenez un dreptunghi mereu peste ca sa acopar ultimul numar, apoi
                        //desenez nr nou citit
                        int xBarStart = latimeButon + 31 + textwidth("Scrie costul si apasa ENTER:");
                        int yBarStart = screenHeight - 100;
                        bar(xBarStart, yBarStart - 2, xBarStart + 100, yBarStart + textheight("0") + 5);
                        outtextxy(xBarStart, yBarStart, numarCitit);
                    }
                }
                outtextxy(latimeButon + 31 + textwidth("Scrie costul si apasa ENTER:"), screenHeight - 100, numarCitit);
                int nrMuchie = getMuchiePentruClick(nodStart, nodClick);//index muchie dintre cele doua noduri ca sa stim unde adaugam costul
                int costCitit = atoi(numarCitit);//transformam in nr intreg din sir caractere
                if (nrMuchie == -1) {//daca nu exista muchia o adaugam
                    Muchie[++m].nod1 = nodStart;
                    Muchie[m].nod2 = nodClick;
                    nrMuchie = m;
                }
                mat[nodStart][nodClick] = costCitit;//setam cost si in mat de adiacenta
                if (!esteOrientat)mat[nodClick][nodStart] = costCitit;//in ambele sensuri daca nu e orientat
                Muchie[nrMuchie].cost = costCitit;
                nodStart = 0;
                stareCurenta = SETEAZA_COST_1;

            }
            break;
        case MUTARE_NOD:
            if (nodMutat == 0) {
                int nodSelectat = getNodPentruClick(xMouse, yMouse);
                if (nodSelectat != 0) {
                    nodMutat = nodSelectat;
                    strcpy(mesajEroare, "");
                }
            }
            else {
                int xSafe, ySafe;
                getPozitieLegala(xMouse, yMouse, xSafe, ySafe);
                if (estePozitieNodValida(xSafe, ySafe, nodMutat)) {
                    Noduri[nodMutat].x = xSafe;
                    Noduri[nodMutat].y = ySafe;
                    nodMutat = 0;
                    strcpy(mesajEroare, "");
                }
                else {
                    strcpy(mesajEroare, "Prea aproape de alt nod!");
                    Beep(300, 300);
                }
            }
            break;
        case STERGE_NOD:
            if (nodClick != 0) {
                stergeNodLogica(nodClick);
                resetNoduriSiMuchii();
            }
            break;
        case STERGE_MUCHIE_1:
            if (nodClick != 0) {
                if (nodStart == 0) {
                    nodStart = nodClick;
                    Noduri[nodStart].viz = 1;
                }
                else {
                    if (nodClick != nodStart) {
                        if (mat[nodStart][nodClick] != 0) {
                            stergeMuchieLogica(nodStart, nodClick);
                            strcpy(mesajEroare, "");
                        }
                        else {
                            strcpy(mesajEroare, "Nu exista muchie intre aceste doua noduri");
                        }
                        Noduri[nodStart].viz = 0;
                        nodStart = 0;
                    }
                }
            }
            break;
        case START_DFS:
            if (nodClick != 0) {//nod valid
                dfs(nodClick);
                stareCurenta = NEUTRU;
                strcpy(mesajEroare, "");
            }
            break;
        case START_BFS:
            if (nodClick != 0) {//nod valid
                bfs(nodClick);
                stareCurenta = NEUTRU;
                strcpy(mesajEroare, "");
            }
            break;
        case DIJKSTRA:
            if (nodClick != 0) {
                dijkstraAlgoritm(nodClick);
            }
            break;
        case PRIM:
            if (nodClick != 0) {
                PrimAlgoritm(nodClick);
            }
            break;
        case BIPARTIT:
            if (nodClick != 0) {
				eBipartit = true;
				culoareNodBipartit[nodClick] = 1;
                dfsBipartit(nodClick,1);
                if (!eBipartit)
                {
                    setcolor(RED);
                    settextstyle(BOLD_FONT, HORIZ_DIR, 3);
                    outtextxy(screenWidth / 2 - 100, screenHeight / 2, "Componenta nu e bipartita!");
                    delay(1000);
                }
                else
                {
                    setcolor(GREEN);
                    settextstyle(BOLD_FONT, HORIZ_DIR, 3);
                    outtextxy(screenWidth / 2 - 100, screenHeight / 2, "Componenta e bipartita!");
                    delay(1000);
                }
                for (int i = 1; i <= n; i++)
                {
                    if(culoareNodBipartit[i]==-1)
						Noduri[i].viz = 0;
					if (culoareNodBipartit[i] == 0)
                        Noduri[i].viz = 2;
                    else if (culoareNodBipartit[i] == 1)
						Noduri[i].viz = 1;
                }
                stareCurenta = NEUTRU;
                strcpy(mesajEroare, "");
            }
			break;
        default:
            break;
        }
    }
    else if (xMouse >= 10 && xMouse <= latimeButon + 10)//butoane stanga
    {
        if (yMouse >= 2 * H && yMouse <= 3 * H - 10) {//apasam pe butonul adauganod
            stareCurenta = ADAUGA_NOD;//dupa coordonate isi da seama pe ce  buton se apasa
            resetNoduriSiMuchii();
        }
        else if (yMouse >= 3 * H && yMouse <= 4 * H - 10) {//apasam pe butonul adugamuchie
            stareCurenta = ADAUGA_MUCHIE_1;
            resetNoduriSiMuchii();
        }
        else if (yMouse >= 4 * H && yMouse <= 5 * H - 10) {//adauga cost
            stareCurenta = SETEAZA_COST_1;
            resetNoduriSiMuchii();
        }
        else if (yMouse >= 5 * H && yMouse <= 6 * H - 10) {//aranjare cerc
            resetNoduriSiMuchii();
            int centruX = screenWidth / 2;
            int centruY = screenHeight / 2;
            int r = min(screenWidth, screenHeight) / 2 - razaNod - 100;
            for (int i = 1; i <= n; i++) {
                double angle = (2 * PI * (i - 1)) / n;
                Noduri[i].x = centruX + r * cos(angle);
                Noduri[i].y = centruY + r * sin(angle);
            }
            stareCurenta = NEUTRU;
        }
        else if (yMouse >= 6 * H && yMouse <= 7 * H - 10) {//mutare nod
            stareCurenta = MUTARE_NOD;
            nodMutat = 0;
        }
        else if (yMouse >= 7 * H && yMouse <= 8 * H - 10) {
            stareCurenta = STERGE_NOD;
        }
        else if (yMouse >= 8 * H && yMouse <= 9 * H - 10) {
            stareCurenta = STERGE_MUCHIE_1;
        }
        else if (yMouse >= 9 * H && yMouse <= 10 * H - 10) {
            stareCurenta = SALVARE_GRAF;
            saveGraf();
            stareCurenta = NEUTRU;
        }
        else if (yMouse >= 10 * H && yMouse <= 11 * H - 10) {
            stareCurenta = LOAD_GRAF;
            loadGraf();
            stareCurenta = NEUTRU;
        }
        //butoane iesire
        else if (yMouse >= screenHeight - 150 && yMouse <= screenHeight - 150 + inaltimeButon) {//buton reset
            for (int i = 1; i <= n; i++) {
                for (int j = 1; j <= n; j++) {
                    mat[i][j] = 0;//se scot toate muchiile
                }
            }
            resetNoduriSiMuchii();
            n = 0;//nr noduri 0
            m = 0;//nr muchii 0
            stareCurenta = NEUTRU;
        }
        else if (yMouse >= screenHeight - 100 && yMouse <= screenHeight - 100 + inaltimeButon) {//apasam pe butonul iesire
            closegraph();
            return 0;
        }
    }
    else if (xMouse >= xDR && xMouse <= screenWidth - 15)//butoane dreapta
    {
        if (yMouse >= 2 * H && yMouse <= 3 * H - 10) {
            stareCurenta = START_DFS;
            resetNoduriSiMuchii();
        }
        else if (yMouse >= 3 * H && yMouse <= 4 * H - 10) {
            stareCurenta = START_BFS;
            resetNoduriSiMuchii();
        }
        else if (yMouse >= 4 * H && yMouse <= 5 * H - 10) {
            if (stareCurenta != ROY_FLOYD)
            {
                resetNoduriSiMuchii();
                royFloyd();
                stareCurenta = ROY_FLOYD;
            }
            else
            {
                stareCurenta = NEUTRU;
                strcpy(mesajEroare, "");
            }
        }
        else if (yMouse >= 5 * H && yMouse <= 6 * H - 10) {
            stareCurenta = DIJKSTRA;
            resetNoduriSiMuchii();
        }
        else if (yMouse >= 6 * H && yMouse <= 7 * H - 10) {
            stareCurenta = BIPARTIT;
            resetNoduriSiMuchii();
            for(int i=1;i<=n;i++)
				culoareNodBipartit[i] = -1;
            if (esteOrientat)
            {
                for(int i=1;i<=n;i++)
                    for(int j=1;j<=n;j++)
                        if(mat[i][j]==1||mat[j][i]==1)
                            matBipartit[i][j]=1;
                        else
							matBipartit[i][j] = 0;
            }
            else
            {
                for(int i=1;i<=n;i++)
                    for(int j=1;j<=n;j++)
						matBipartit[i][j] = mat[i][j];
            }
        }
        if (!esteOrientat)
        {
            if (yMouse >= 7 * H && yMouse <= 8 * H - 10) {
                stareCurenta = PRIM;
                resetNoduriSiMuchii();
            }
            else if (yMouse >= 8 * H && yMouse <= 9 * H - 10) {
                stareCurenta = KRUSKAL;
                resetNoduriSiMuchii();
                kruskalAlgoritm();
            }
            else if (yMouse >= 9 * H && yMouse <= 10 * H - 10) {
                if (stareCurenta == HIGHLIGHT_CC)
                {
                    stareCurenta = NEUTRU;
                    resetNoduriSiMuchii();
                }
                else
                {
                    stareCurenta = HIGHLIGHT_CC;
                    resetNoduriSiMuchii();
                    componenteConexe();
                }
            }
            else if (yMouse >= 10 * H && yMouse <= 11 * H - 10) {
                if (stareCurenta == PUNCTE_ARTICULATIE) {
                    stareCurenta = NEUTRU;
                    resetNoduriSiMuchii();
                }
                else {
                    stareCurenta = PUNCTE_ARTICULATIE;
                    resetNoduriSiMuchii();
                    findPuncteArt();
                }
            }
        }
        else {//pt grafuri orientate
            if (yMouse >= 7 * H && yMouse <= 8 * H - 10) {
                if (stareCurenta == HIGHLIGHT_TC)
                {
                    stareCurenta = NEUTRU;
                    resetNoduriSiMuchii();
                }
                else
                {
                    stareCurenta = HIGHLIGHT_TC;
                    resetNoduriSiMuchii();
                    kosaraju();
                }
            }
        }
        //butoane iesire
        if (yMouse >= screenHeight - 100 && yMouse <= screenHeight + inaltimeButon - 100) {//apasam pe butonul inapoi
            apasatButonInapoi = true;
        }
    }
    return true;
}
int main() {
    screenWidth = GetSystemMetrics(SM_CXSCREEN);
    screenHeight = GetSystemMetrics(SM_CYSCREEN);//dimensiunile ecranului
    initwindow(screenWidth, screenHeight, "Meniu Grafuri", -3, -3);
    int xMouse, yMouse;
    while (1) {//state machine pana se apasa pe buton iesire ruleaza permanent
        n = 0; m = 0;
        stareCurenta = NEUTRU;
        strcpy(mesajEroare, "");
        for (int i = 0; i < 101; i++) {
            Muchie[i].culoare = 0;
            for (int j = 0; j < 101; j++) {
                mat[i][j] = mat[j][i] = 0;
                Noduri[i].viz = 0;
            }
        }
        setactivepage(0);
        setvisualpage(0);

        bool amSelectatOrientare = false;
        while (!amSelectatOrientare) {//meniu start
            deseneazaStart();
            if (ismouseclick(WM_LBUTTONDOWN)) {
                getmouseclick(WM_LBUTTONDOWN, xMouse, yMouse);
                int midX = screenWidth / 2 - latimeButon / 2;
                int midY = screenHeight / 2;
                if (xMouse >= midX && xMouse <= midX + latimeButon) {
                    if (yMouse >= midY - 60 && yMouse <= midY - 60 + inaltimeButon) {//apasam buton graf orientat
                        esteOrientat = 1;
                        amSelectatOrientare = 1;
                    }
                    else if (yMouse >= midY && yMouse <= midY + inaltimeButon) {//appasam buton graf neorientat
                        esteOrientat = 0;
                        amSelectatOrientare = 1;
                    }
                    else if (yMouse >= midY + 60 && yMouse <= midY + 60 + inaltimeButon)
                    {
                        bool fereastraInfo = true;
                        int X = screenWidth / 2;
                        int Y = screenHeight / 2;
                        int pg = getvisualpage();
                        while (fereastraInfo)
                        {
							setactivepage(1 - pg);
                            setfillstyle(SOLID_FILL, LIGHTGRAY);
                            bar(X - 500, Y - 400, X + 500, Y + 200);
                            setcolor(BLUE);
                            rectangle(X - 500, Y - 400, X + 500, Y + 200);
                            setfillstyle(SOLID_FILL, RED);
                            bar(X + 450, Y - 400, X + 500, Y - 350);
                            setbkcolor(RED);
                            setcolor(BLACK);
							settextstyle(BOLD_FONT, HORIZ_DIR, 5);
							outtextxy(X + 463, Y - 395, "X");
							setbkcolor(LIGHTGRAY);
							setcolor(BLACK);
                            settextstyle(BOLD_FONT, HORIZ_DIR, 4);
                            outtextxy(X - 250, Y - 320, "Informatii despre proiect");
							settextstyle(BOLD_FONT, HORIZ_DIR, 3);
							outtextxy(X - 460, Y - 250, "Acesta este un program de vizualizare si simulare");
                            outtextxy(X - 460, Y - 220, "a algoritmilor pe grafuri.");
							outtextxy(X - 460, Y - 180, "In stanga se afla butoane pentru formatarea grafului, cum");
							outtextxy(X - 460, Y - 150, "ar fi adaugarea si stergerea nodurilor si a muchiilor, mutarea");
							outtextxy(X - 460, Y - 120, "acestora sau salvarea si incarcarea unui graf din fisier.");
							outtextxy(X - 460, Y - 80, "In dreapta se afla butoane pentru rularea algoritmilor, iar ");
							outtextxy(X - 460, Y - 50, "acestia difera in functie de graf (daca este orientat sau nu).");
                            if (ismouseclick(WM_LBUTTONDOWN))
                            {
                                int XM, YM;
								getmouseclick(WM_LBUTTONDOWN, XM, YM);
                                if(XM>= X + 450 && XM <= X + 500 && YM >= Y - 400 && YM <= Y - 350)
                                {
                                    fereastraInfo = false;
								}
                            }
							setvisualpage(1 - pg);
                            pg = 1 - pg;
                            delay(250);
                        }
                    }
                    else if (yMouse >= midY + 120 && yMouse <= midY + 120 + inaltimeButon) {//apasam buton iesire
                        amSelectatOrientare = 1;
                        closegraph();
                        return 0;
                    }
                }
            }
            delay(250);
        }
        bool apasatButonInapoi = false;
        bool trebuieDesenare = true;
        int oldMouseX = 0, oldMouseY = 0;//coordonate anterioare mouse, pt updatare in timp real
        while (apasatButonInapoi == false) {//daca nu apasam pe inapoi ramanem in scena principala
            if (trebuieDesenare) {//doar daca dam click deseneaza scena ca sa nu umple stiva Windowsului -> crash grafic
                deseneazaScena();
                trebuieDesenare = false;
            }
            if (stareCurenta == ADAUGA_MUCHIE_2) {
                if (mousex() != oldMouseX || mousey() != oldMouseY) {
                    trebuieDesenare = true;//daca se modifica coordonatele, si sunt in mod adaugare muchie, desenez scena
                    oldMouseX = mousex();
                    oldMouseY = mousey();
                }
            }
            if (stareCurenta == MUTARE_NOD) {
                if ((mousex() != oldMouseX || mousey() != oldMouseY) && nodMutat != 0) {
                    int xSafe, ySafe;
                    getPozitieLegala(mousex(), mousey(), xSafe, ySafe);
                    Noduri[nodMutat].x = xSafe;
                    Noduri[nodMutat].y = ySafe;
                    trebuieDesenare = true;
                    oldMouseX = xSafe;
                    oldMouseY = ySafe;
                }
            }
            if (ismouseclick(WM_LBUTTONDOWN)) { //detecteaza click
                strcpy(mesajEroare, "");
                trebuieDesenare = true;
                Noduri[nodStart].viz = 0;//aici de exemplu selectez un nod cand adaug primul nod dintr-o muchie si il colorez verde, vreau ca la urmatoareaza
                //instanta a programului sa nu mai fie colorat, pt ca presupunem ca s-a ales ceva
                getmouseclick(WM_LBUTTONDOWN, xMouse, yMouse);
                if (checkRF(xMouse, yMouse)) continue;
                if (!handleClick(xMouse, yMouse, apasatButonInapoi))
                    return 0;
            }
            delay(100);//delay ca sa nu ruleze procesor 100%
        }
    }
    closegraph();
    return 0;
}
