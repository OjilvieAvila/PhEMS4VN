//feromona

#include <iostream>
#include <sstream>
#include <string>
#include <cstring>
#include <fstream>

#include "veins_inet/VeinsInetSampleApplication.h"

#include "inet/common/ModuleAccess.h"
#include "inet/common/packet/Packet.h"
#include "inet/common/TagBase_m.h"
#include "inet/common/TimeTag_m.h"
#include "inet/networklayer/common/L3AddressResolver.h"
#include "inet/networklayer/common/L3AddressTag_m.h"
#include "inet/transportlayer/contract/udp/UdpControlInfo_m.h"

#include <unistd.h>
#include <cmath>

#include "veins_inet/VeinsInetSampleMessage_m.h"

#define pck_size 500
#define verbal 1
#define proto_segregation "AA00:"
#define proto_notification "BB00:"
#define movil 1
#define fija 0
#define pi 3.14159265359
#define degradacion 1
#define umbral_desvio 15
#define MAX_PHER 10
#define num_designated_incs 1
#define cardinalidad_E 500
#define cardinalidad_FE 5
#define cardinalidad_ME cardinalidad_E-cardinalidad_FE
#define cardinalidad_ROUTES 10
#define incidentes_aleatorios 0
#define max_me 500

#define my_file_name "feromona.csv"

using namespace inet;

//variables para determinar tiempo de simulacion, incio y fin de incidente, periodos de reafirmacion y notificacion

//estas variables todavia no se si tengan caso
unsigned long t_inicio_sim = 0;
unsigned long t_fin_sim = 300;

//variables temporales para incidente
unsigned long segregar = 50;

//variables temporales de feromona: periodos de vida y tiempos de notificacion
unsigned long vida_pher = 60;
unsigned long incremento = 5;

struct
{
    unsigned long mi_id; // se requiere id o con el indice del getParent...
    unsigned short p; //contador interno de incidentes
    unsigned short inc_act; // si esta entidad tiene incidente activo
    unsigned short fail_designated; //en que entrada del arreglo de incidentes estan los datos
    unsigned short index_fail; //entrada en la estructura de incidentes
    unsigned long t_inicio; //tiempo de simulacion en que entran al ambiente
    unsigned long t_me; //el tiempo que tiene cada una de las entidades moviles que fallan
} ME_data[cardinalidad_ME];

//arreglo de incidentes designados
struct me_with_incident
{
    unsigned long designated_me;
    unsigned long t_start_inc;
    unsigned long t_end_inc;

} incs[num_designated_incs]; //alt_incs[num_designated_incs], incs[num_designated_incs];

//conjunto de entidades que fallan
std::set<unsigned long> ME_inc;

//variables para el incidente
struct
{
    unsigned long mi_id;
    unsigned int no_inc;
    double coord_x;
    double coord_y;
    unsigned long t_inicio;
    unsigned long t_fin;
    unsigned long delta_t_inc;
    //unsigned short Stt;
    //bool local;
} incidentes[10]; //incidentes4[10];

//variables e historial de feromonas para cada entidad fija
struct
{
    unsigned long mi_id;
    unsigned long id_me;
    unsigned int num_inc_lcl;
    double me_coord_x;
    double me_coord_y;
    unsigned long phi_alpha;
    unsigned long phi_omega;
    int az01 = 0;
    int az02 = 90;
    int az03 = 180;
    int az04 = 270;
    float in01;
    float in02;
    float in03;
    float in04;
    unsigned long timer_value;
} feromonas[MAX_PHER][cardinalidad_FE], feromona_rx;

///variable para pasar payload entre eventos/procesos?
std::string mi_payload_pasar[cardinalidad_FE];

struct
{
    //variables temporales de la feromona activa
    unsigned long countdown_t;
    unsigned long delta_pher;
    unsigned long t_alpha;
    unsigned long t_beta;
    unsigned long t_gamma;
    unsigned long t_omega;

    //banderas individuales que determinan si la feromona esta activa y si fue segregada o reafirmada
    unsigned short first_time = 1;
    unsigned short pher_act = 0;

    //variables para pasar datos entre hilos/procesos de la misma entidad
    unsigned short update_pher = 0;
    unsigned short total_feromonas = 0;

    //cadena para pasar edge entre hilos/procesos en RSUs
    std::string temp_edge;
} FE_data[cardinalidad_FE];

//+++variables metricas a archivo
unsigned long tiempo_inicio[max_me];
unsigned long tiempo_rx[max_me];
unsigned short inicial[max_me];
unsigned short inc_activo[max_me];

unsigned long ocurrencia[max_me];
unsigned long recepciones[max_me];
unsigned long reenvios[max_me];
unsigned short activado[max_me];
float longitud_payload;
unsigned long longitud_header;
std::string pck;
std::string all_data;
double coordenada_x, coordenada_y;
double mi_x_rx[max_me], mi_y_rx[max_me] , mi_x_actual[max_me], mi_y_actual[max_me];
unsigned long coordenada_t_alpha, coordenada_t_omega, mi_tiempo_actual[max_me];
double distancia_manhattan[max_me];
unsigned short desvio[max_me];
std::fstream my_file;
unsigned long rec_backup;
//---variables metricas a archivo

Define_Module(VeinsInetSampleApplication);

//inicio funciones propias

unsigned long to_azimuth (float angulo)
{
    unsigned long azimuth;
    if (angulo == 90) // caso sobre el eje +y
        azimuth = 0;
    else if (angulo == 180) // caso sobre el eje -x
        azimuth = 270;
    else if (angulo == 0) // caso sobre el eje +x
        azimuth = 90;
    else if (angulo == -90) // caso sobre el eje -y
        azimuth = 180;
    else if ((0 < angulo) && (angulo < 90)) // caso cuadrante I
        azimuth = 90 - (angulo);
    else if ((180 > angulo) && (angulo > 90)) // caso cuadrante II
        azimuth = 450 - (angulo);
    else if ((-180 < angulo) && (angulo < 90)) // caso cuadrante III
        azimuth = 270 - (180 + angulo);
    else // caso cuadrante IV
        azimuth = 90 - (angulo);
    return azimuth;
}

void genera_incidentes (unsigned short max_inc)
{
    srand((unsigned) time(NULL));
    unsigned short k, k2;
    me_with_incident temp_inc[max_inc];

    for (k = 0; k < max_inc; k++)
    {
        unsigned long random_index = (rand() % (cardinalidad_ME - cardinalidad_FE)) + cardinalidad_FE;
        unsigned long random_t_init = (rand() % 40) + (floor(random_index / cardinalidad_ROUTES) * 60);
        unsigned long random_t_end = (rand() % 180) + random_t_init;
        if (t_fin_sim <= random_t_end)
            random_t_end = t_fin_sim - 15;
        if (k > 1)
        {
            if (incs[k - 1].designated_me == random_index)
            {
                if ((incs[k - 1].designated_me % cardinalidad_ROUTES) <= 5)
                    random_index = random_index + 2;
                else
                    random_index = random_index - 2;
            }
        }

        temp_inc[k].designated_me = random_index;
        temp_inc[k].t_start_inc = random_t_init;
        temp_inc[k].t_end_inc = random_t_end;

        if (verbal)
        {
            EV_INFO << "estructura sin orden en indice " << endl;
            EV_INFO << "indice: " << temp_inc[k].designated_me << endl;
            EV_INFO << "t inicio: " << temp_inc[k].t_start_inc << endl;
            EV_INFO << "t fin: " << temp_inc[k].t_end_inc << endl;
        }

        ME_inc.insert(random_index); //agregamos al conjunto que en automatico ordena
    }

    //ordenar de acuerdo al conjunto!!
    for (k = 0; k < max_inc; k++)
    {
        auto it = next(ME_inc.begin(), k);
        k2 = 0;

        while (*it != temp_inc[k2].designated_me)
            k2++;

        incs[k] = temp_inc[k2];
    }
}

void llena_incidentes (void) //incidentes prederminados
{
    incs[0].designated_me = 0 + cardinalidad_FE;
    incs[0].t_start_inc = 21;
    incs[0].t_end_inc = 221;
    ME_inc.insert(incs[0].designated_me);

    /*incs[1].designated_me = 24 + cardinalidad_FE;
    incs[1].t_start_inc = 140;
    incs[1].t_end_inc = 252;
    ME_inc.insert(incs[1].designated_me);

    incs[2].designated_me = 41 + cardinalidad_FE;
    incs[2].t_start_inc = 300;
    incs[2].t_end_inc = 500;
    ME_inc.insert(incs[2].designated_me);

    incs[3].designated_me = 45 + cardinalidad_FE;
    incs[3].t_start_inc = 263;
    incs[3].t_end_inc = 370;
    ME_inc.insert(incs[3].designated_me);

    incs[4].designated_me = 94 + cardinalidad_FE;
    incs[4].t_start_inc = 560;
    incs[4].t_end_inc = 672;
    ME_inc.insert(incs[4].designated_me);*/
}

void archivar (int designated)
{
    my_file << "resumen+++" << endl;
    my_file << "id entidad que provoca incidente: " << endl;
    my_file << incs[0].designated_me << endl;

    my_file << "lugar de incidente (x,y): " << endl;
    my_file << coordenada_x << "," << coordenada_y << endl;

    my_file << "tiempo de inicio y fin de incidente: " << endl;
    my_file << coordenada_t_alpha << "," << coordenada_t_omega << endl;

    my_file << "cadena payload: " << endl;
    my_file << pck << endl;

    my_file << "longitud header: " << endl;
    my_file << longitud_header << endl;

    my_file << "longitud payload: " << endl;
    my_file << longitud_payload << endl;

    my_file << "datos completos del paquete: " << endl;
    my_file << all_data << endl;

    my_file << "veces que se envio mensaje de emergencia u ocurrencia: " << endl;
    my_file << ocurrencia[designated] << endl;

    my_file << "+++ id, habilitado, tiempo inicio operaciones, paquetes recibidos, reenvios, mi x, mi y, distancia al recibir, tiempo de recepcion, si hago desvio: " << endl;
    int rec;
    for (rec = 0;rec < max_me; rec++)
    {
        my_file << rec << "," << activado[rec] << "," << tiempo_inicio[rec] << "," << recepciones[rec] << "," ;
        my_file << reenvios[rec] << "," << mi_x_rx[rec] << "," << mi_y_rx[rec] << "," << distancia_manhattan[rec] << "," << tiempo_rx[rec] << "," ;
        my_file << desvio[rec] << endl;

        if ((rec > incs[0].designated_me) && (!activado[rec]))
            break;
    }
    my_file << "--- " << endl;

    my_file.close();
}

float distanciaM (float x1, float y1, float x2, float y2)
{
    float dist;
    dist = std::fabs((x1 - x2)) + std::fabs((y1 - y2));
    return dist;
}

bool en_rango (float x1, float y1, float x2, float y2)
{
    float dist;
    float x = std::pow((x1 - x2), 2);
    float y = std::pow((y1 - y2), 2);
    float radical = x + y;

    dist = std::sqrt(radical);
    if (dist <= 80.7757680) //distancia obtenida con aplicacion gatcomsumo
        return true;
    else
        return false;
}

//fin funciones propias


VeinsInetSampleApplication::VeinsInetSampleApplication()
{
}

bool VeinsInetSampleApplication::startApplication()
{
    activado[getParentModule()->getIndex()] = 1;
    tiempo_inicio[getParentModule()->getIndex()] = simTime().dbl();

    EV_INFO << "Inicio operaciones, mi id: " << getParentModule()->getIndex() << endl;

    if (verbal)
    {
        EV_INFO << "constantes " << endl;
        EV_INFO << "E: " << cardinalidad_E << endl;
        EV_INFO << "FE: " << cardinalidad_FE << endl;
        EV_INFO << "ME: " << cardinalidad_ME << endl;
        if (getParentModule()->getIndex() < cardinalidad_FE)
            EV_INFO << "mi indice en arreglo FE: " << getParentModule()->getIndex() << endl;
        else
            EV_INFO << "mi indice en arreglo ME: " << getParentModule()->getIndex() - 2 << endl;
    }

    unsigned long formula_card_ME = ((ceil(t_fin_sim - t_inicio_sim) / 60) * cardinalidad_ROUTES) + cardinalidad_FE + 1;

    if (verbal)
        EV_INFO << "calculo de entidades moviles por formula " << formula_card_ME << endl;

    if (getParentModule()->getIndex() == 0) //por definir que entidades moviles han de fallar e ingresar los primeros indices en el conjunto de
    //entidades fijas??
    {


        if (incidentes_aleatorios)
            genera_incidentes(num_designated_incs);

        else
            llena_incidentes();

        if (verbal)
        {
            int k;
            for (k = 0; k < num_designated_incs; k++)
            {
                auto it = next(ME_inc.begin(), k);
                EV_INFO << " " << endl;
                EV_INFO << "entidad que falla: " << incs[k].designated_me << " " << *it << endl;
                EV_INFO << "tiempo en que inicia falla: " << incs[k].t_start_inc << endl;
                EV_INFO << "tiempo en que termina falla: " << incs[k].t_end_inc << endl;

                ME_data[incs[k].designated_me - cardinalidad_FE].fail_designated = 1;
                ME_data[incs[k].designated_me - cardinalidad_FE].index_fail = k;
            }
        }
        //llenar las entradas de las entidades que van a fallar!!
    }

    ///++++++++++++++++++++++++++++++++++++++++++++CODIGO ENTIDADES FIJAS inicio
    if (getParentModule()->getIndex() < cardinalidad_FE)
    {

        EV_INFO << "aqui 1: mi id: " << getParentModule()->getIndex() << endl;

        if (getParentModule()->getIndex() == 0)
        {
            my_file.open(my_file_name, std::ios::out);
        }

        auto callback = [this]()
        {
            EV_INFO << "aqui 1.5: mi id: " << getParentModule()->getIndex() << endl;

            if ((getParentModule()->getIndex() == 0) && (FE_data[0].pher_act) && (((incs[0].t_start_inc - int(simTime().dbl()) + 1) % incremento) == 0))
            //if ((getParentModule()->getIndex() == 0) && (FE_data[0].pher_act) && (((incs[0].t_start_inc - int(simTime().dbl()) + 1) % incremento) == 0))
            //if ((getParentModule()->getIndex() == 0) && (FE_data[0].pher_act) && (((incs[0].t_start_inc - int(std::floor(simTime().dbl())) + 1) % incremento) == 0))
            {

                int rec;// = 0 + inc_activo[incs[0].designated_me];

                if (rec_backup == 0)
                    rec = 0 + incs[0].designated_me;
                    //rec = 0 + inc_activo[incs[0].designated_me];
                else
                    rec = rec_backup;

                unsigned long paquetes_recibidos = 0;
                unsigned long entidades_rango = 0;
                float x_rsu = mobility->getCurrentPosition().x;
                float y_rsu = mobility->getCurrentPosition().y;

                EV_INFO << "coordenadas RSU: " << x_rsu << "," << y_rsu << endl;

                my_file << "tiempo actual: " << simTime().dbl() << " ocurrencia numero: " << ocurrencia[getParentModule()->getIndex()] << endl;
                my_file << "+++ id, habilitado, tiempo inicio operaciones, paquetes recibidos, reenvios, mi x actual, mi y actual, tiempo de coordenadas, si hago desvio: " << endl;
                do
                {
                    my_file << rec << "," << activado[rec] << "," << tiempo_inicio[rec] << "," << recepciones[rec] << "," ;
                    my_file << reenvios[rec] << "," << mi_x_actual[rec] << "," << mi_y_actual[rec] << "," << mi_tiempo_actual[rec] << ",";
                    my_file << desvio[rec] << endl;

                    if ((recepciones[rec] > 0) && (activado[rec] > 0) && (rec > incs[0].designated_me))
                        paquetes_recibidos++;

                    if (en_rango(mi_x_actual[rec], mi_y_actual[rec], x_rsu, y_rsu))
                        entidades_rango++;

                    rec++;
                }
                while (activado[rec] != 0);

                if (entidades_rango)
                    rec_backup = rec;

                my_file << "paquetes recibidos, entidades en rango " << endl;
                my_file << paquetes_recibidos << "," << entidades_rango << endl;
                my_file << endl;
            }

            if (FE_data[getParentModule()->getIndex()].pher_act)
            {
                EV_INFO << "aqui 3 simtime beta: " << FE_data[getParentModule()->getIndex()].t_beta << endl;

                //colorear la RSU
                float current_intensity = (float)FE_data[getParentModule()->getIndex()].countdown_t / vida_pher;
                EV_INFO << "intensidad actual " << current_intensity << endl;

                if ((1 >= current_intensity) && (current_intensity > 0.75))
                    getParentModule()->getDisplayString().setTagArg("i", 1, "red");
                else if ((0.75 >= current_intensity) && (current_intensity > 0.50))
                    getParentModule()->getDisplayString().setTagArg("i", 1, "orange");
                else if ((0.50 >= current_intensity) && (current_intensity > 0.25))
                    getParentModule()->getDisplayString().setTagArg("i", 1, "yellow");
                else
                    getParentModule()->getDisplayString().setTagArg("i", 1, "green");

                if (FE_data[getParentModule()->getIndex()].update_pher)
                {
                    //llenamos la estructura de la feromona con datos del incidente
                    feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].mi_id = getParentModule()->getIndex();

                    int i = 8, j = 0;
                    std::string temp_me;
                    std::string temp_inc;
                    std::string temp_x;
                    std::string temp_y;
                    std::string temp_time;

                    do //obtener la entidad origen
                    {
                        temp_me[j] = mi_payload_pasar[getParentModule()->getIndex()][i];
                        i++;
                        j++;
                    }
                    while (mi_payload_pasar[getParentModule()->getIndex()][i] != ':');
                    temp_me[j] = '\0';
                    EV_INFO << " id entidad " << temp_me.data() << endl;
                    feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].id_me = std::strtoul(temp_me.data(), NULL, 0); //unsigned long

                    i++;
                    j = 0;
                    do //obtener el numero de incidente
                    {
                        temp_inc[j] = mi_payload_pasar[getParentModule()->getIndex()][i];
                        i++;
                        j++;
                    }
                    while (mi_payload_pasar[getParentModule()->getIndex()][i] != ':');
                    temp_inc[j] = '\0';
                    EV_INFO << " numero local incidente " << temp_inc.data() << endl;
                    feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].num_inc_lcl = std::strtoul(temp_inc.data(), NULL, 0); //unsigned long

                    i++;
                    j = 0;
                    do //obtener coordenada x de incidente
                    {
                        temp_x[j] = mi_payload_pasar[getParentModule()->getIndex()][i];
                        i++;
                        j++;
                    }
                    while (mi_payload_pasar[getParentModule()->getIndex()][i] != ':');
                    temp_x[j] = '\0';
                    EV_INFO << " coordenada x del incidente " << temp_x.data() << endl;
                    //feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_x = std::strtol(temp_x.data(), NULL, 0); //este es entero +-
                    feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_x = std::stof(temp_x.data()); //este es entero +-

                    i++;
                    j = 0;
                    do //obtener coordenada y de incidente
                    {
                        temp_y[j] = mi_payload_pasar[getParentModule()->getIndex()][i];
                        i++;
                        j++;
                    }
                    while (mi_payload_pasar[getParentModule()->getIndex()][i] != ':');
                    temp_y[j] = '\0';
                    EV_INFO << " coordenada y del incidente " << temp_y.data() << endl;
                    feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_y = std::stof(temp_y.data()); //este es entero +-

                    i++;
                    j = 0;
                    do //obtener tiempo de inicio de incidente
                    {
                        temp_time[j] = mi_payload_pasar[getParentModule()->getIndex()][i];
                        i++;
                        j++;
                    }
                    while (mi_payload_pasar[getParentModule()->getIndex()][i] != ':');
                    temp_time[j] = '\0';
                    EV_INFO << " tiempo de inicio del incidente " << temp_time.data() << endl;
                    feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].phi_alpha = std::strtoul(temp_time.data(), NULL, 0); //unsigned long

                    i = i + 2;
                    j = 0;
                    do //obtener edge del incidente
                    {
                        FE_data[getParentModule()->getIndex()].temp_edge[j] = mi_payload_pasar[getParentModule()->getIndex()][i];
                        i++;
                        j++;
                    }
                    while (mi_payload_pasar[getParentModule()->getIndex()][i] != ';');
                    FE_data[getParentModule()->getIndex()].temp_edge[j] = '\0';
                    EV_INFO << " edge del incidente " << FE_data[getParentModule()->getIndex()].temp_edge.data() << endl;

                    EV_INFO << "copia de payload recibido: " << mi_payload_pasar[getParentModule()->getIndex()] << endl;
                    EV_INFO << "enviado desde la entidad movil " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].id_me << endl;
                    EV_INFO << "numero de incidente local " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].num_inc_lcl << endl;
                    EV_INFO << "coordenada x del incidente " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_x << endl;
                    EV_INFO << "coordenada y del incidente " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_y << endl;
                    EV_INFO << "tiempo de inicio del incidente " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].phi_alpha << endl;
                    EV_INFO << "edge incidente " << FE_data[getParentModule()->getIndex()].temp_edge.data() << endl;

                    //llenar los campos de intensidades
                    float mi_coord_x = mobility->getCurrentPosition().x;
                    float mi_coord_y = mobility->getCurrentPosition().y;
                    EV_INFO << "mi coordenada x: " << mi_coord_x << " mi coordenada y: " << mi_coord_y << endl;

                    //float angulo = atan2(-50,-50)* 180 / pi; //linea de prueba NO BORRAR
                    //float angulo = atan2((mi_coord_y - 100),(150 - mi_coord_x)) * 180 / pi; //linea de prueba NO BORRAR
                    float angulo = atan2((mi_coord_y - feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_y),(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_x) - mi_coord_x) * 180 / pi;

                    unsigned long azimuth = to_azimuth (angulo);

                    EV_INFO << "angulo de la pendiente al incidente con respecto al eje x " << angulo << endl;
                    EV_INFO << "angulo de azimuth con respecto al norte " << azimuth << endl;
                }

                if ((FE_data[getParentModule()->getIndex()].t_gamma-FE_data[getParentModule()->getIndex()].countdown_t) < FE_data[getParentModule()->getIndex()].t_gamma)
                {
                    EV_INFO << "aqui 4 countdown: " << FE_data[getParentModule()->getIndex()].countdown_t << endl;

                    if ((FE_data[getParentModule()->getIndex()].countdown_t % incremento) == 0)
                    {
                        EV_INFO << "aqui 5 multiplo de 5: " << FE_data[getParentModule()->getIndex()].countdown_t % incremento << endl;

                        std::ostringstream mi_feromona;
                        std::string enti_tipo = std::to_string(0) + "::"; //preambulo
                        std::string mi_id_str = std::to_string(getParentModule()->getIndex()) + ":";
                        std::string id_me_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].id_me) + ":";
                        std::string no_inc_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].num_inc_lcl) + ":";
                        std::string inc_x_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_x) + ":";
                        std::string inc_y_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].me_coord_y) + ":";
                        std::string phi_alpha_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].phi_alpha) + "::";//datos generales de incidente

                        //agregar intensidades random y calcular la intensidad en el edge del incidente
                        //Y terminamos de llenar la estructura de la feromona para comunicarla
                        srand ((unsigned) time(NULL));
                        float num2[3];
                        for (int i=0;i<3;i++)
                        {
                            unsigned int num1 = (rand() % 150);
                            num2[i] = (float)num1 / 1000;
                        }
                        feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in01 = num2[0];
                        feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in03 = num2[1];
                        feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in04 = num2[2];

                        float intensidad_inc = (float)FE_data[getParentModule()->getIndex()].countdown_t / vida_pher;
                        feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in02 = intensidad_inc;

                        EV_INFO << "intensidad salida azimuth 000: " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in01 << endl;
                        EV_INFO << "intensidad salida azimuth 090: " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in02 << endl;
                        EV_INFO << "intensidad salida azimuth 180: " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in03 << endl;
                        EV_INFO << "intensidad salida azimuth 270: " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in04 << endl;

                        feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].timer_value = FE_data[getParentModule()->getIndex()].countdown_t;

                        std::string in01_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in01) + ":";
                        std::string in02_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in02) + ":";
                        std::string in03_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in03) + ":";
                        std::string in04_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].in04) + "::";
                        std::string timer_str = std::to_string(feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].timer_value) + "::";

                        //creacion del mensaje de la feromona
                        //preambulo
                        mi_feromona << proto_notification;
                        mi_feromona << enti_tipo;

                        //cuerpo de feromona
                        mi_feromona << mi_id_str;
                        mi_feromona << id_me_str;
                        mi_feromona << no_inc_str;
                        mi_feromona << inc_x_str;
                        mi_feromona << inc_y_str;
                        mi_feromona << phi_alpha_str;
                        mi_feromona << in01_str;
                        mi_feromona << in02_str;
                        mi_feromona << in03_str;
                        mi_feromona << in04_str;
                        mi_feromona << timer_str;

                        //edge
                        mi_feromona << FE_data[getParentModule()->getIndex()].temp_edge.data();

                        mi_feromona << ";";
                        mi_feromona << "\0";

                        EV_INFO << "mensaje de feromona a Tx: " << mi_feromona.str().data() << endl;

                        auto payload = makeShared<VeinsInetSampleMessage>();
                        payload->setChunkLength(B(pck_size));
                        payload->setRoadId(mi_feromona.str().data());
                        timestampPayload(payload);

                        auto packet = createPacket("notificar ");
                        packet->insertAtBack(payload);
                        sendPacket(std::move(packet));
                        FE_data[getParentModule()->getIndex()].update_pher = 0;

                        ocurrencia[getParentModule()->getIndex()]++;
                        //ocurrencia[0]++;
                    }
                }
                else
                {
                    FE_data[getParentModule()->getIndex()].first_time = 1;
                    getParentModule()->getDisplayString().setTagArg("i", 1, "white");
                    FE_data[getParentModule()->getIndex()].t_omega = simTime().dbl();
                    FE_data[getParentModule()->getIndex()].delta_pher = FE_data[getParentModule()->getIndex()].t_omega - FE_data[getParentModule()->getIndex()].t_alpha;
                    FE_data[getParentModule()->getIndex()].pher_act = 0;
                    feromonas[FE_data[getParentModule()->getIndex()].total_feromonas][getParentModule()->getIndex()].phi_omega = FE_data[getParentModule()->getIndex()].t_omega;
                    FE_data[getParentModule()->getIndex()].total_feromonas++;
                    EV_INFO << "aqui 6 vida total de feromona: " << FE_data[getParentModule()->getIndex()].delta_pher << endl;
                }
                FE_data[getParentModule()->getIndex()].countdown_t--;
            }
            else
            {
                EV_INFO << "aqui 2 " << getParentModule()->getIndex() << endl;
                if (FE_data[getParentModule()->getIndex()].total_feromonas > 0)
                {
                    EV_INFO << "datos de ultima feromona muerta alpha: " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas-1][getParentModule()->getIndex()].phi_alpha << endl;
                    EV_INFO << "datos de ultima feromona muerta omega: " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas-1][getParentModule()->getIndex()].phi_omega << endl;
                    EV_INFO << "tiempo de vida de ultima feromona muerta: " << feromonas[FE_data[getParentModule()->getIndex()].total_feromonas-1][getParentModule()->getIndex()].phi_omega-feromonas[FE_data[getParentModule()->getIndex()].total_feromonas-1][getParentModule()->getIndex()].phi_alpha << endl;
                }
            }

            if ((getParentModule()->getIndex() == 0) && (simTime().dbl() > (t_fin_sim-1)))
            {
                EV_INFO << "terminar " << endl;

                archivar(getParentModule()->getIndex());
            }
        };
        timerManager.create(veins::TimerSpecification(callback).interval(SimTime(1, SIMTIME_S))); //con esta linea se repite el evento cada incremento en tiempo
    }
    ///--------------------------------------------CODIGO ENTIDADES FIJAS fin
    else
    {
        //iniciar la estructura ME_data
        ME_data[getParentModule()->getIndex() - cardinalidad_FE].mi_id = getParentModule()->getIndex();
        ME_data[getParentModule()->getIndex() - cardinalidad_FE].p = 0;
        ME_data[getParentModule()->getIndex() - cardinalidad_FE].inc_act = 0;
        ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_inicio = simTime().dbl();

        if (ME_data[getParentModule()->getIndex() - cardinalidad_FE].fail_designated)
        {
            EV_INFO << "destinado a fallar: " << getParentModule()->getIndex() << endl;
            EV_INFO << "mi indice en estructura: " << getParentModule()->getIndex() - cardinalidad_FE << endl;
            EV_INFO << "entrada designated: " << ME_data[getParentModule()->getIndex() - cardinalidad_FE].fail_designated << endl;
            EV_INFO << "indice en estructura incidentes: " << ME_data[getParentModule()->getIndex() - cardinalidad_FE].index_fail << endl;

            EV_INFO << "inicia mi fallo en tiempo: " << incs[ME_data[getParentModule()->getIndex() - cardinalidad_FE].index_fail].t_start_inc << endl;
            EV_INFO << "termina mi fallo en tiempo: " << incs[ME_data[getParentModule()->getIndex() - cardinalidad_FE].index_fail].t_end_inc << endl;
        }

        if (ME_inc.find(getParentModule()->getIndex()) != ME_inc.end())
        {
            //despues aca dentro de la condicion ver si es entidad destinada a fallar... en caso que deba hacer incidente SE EJECUTA CALLBACK

            auto callback = [this]()
            {
                ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me = simTime().dbl();

                EV_INFO << "alla 1.5: mi id: " << getParentModule()->getIndex() << endl;

                if ((incs[ME_data[getParentModule()->getIndex() - cardinalidad_FE].index_fail].t_start_inc <= ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me) && (ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me < incs[ME_data[getParentModule()->getIndex() - cardinalidad_FE].index_fail].t_end_inc))
                {
                    if (!ME_data[getParentModule()->getIndex() - cardinalidad_FE].inc_act)
                    {
                        //inicia incidente
                        traciVehicle->setSpeed(0);

                        coordenada_x = mobility->getCurrentPosition().x;
                        coordenada_y = mobility->getCurrentPosition().y;
                        coordenada_t_alpha = simTime().dbl();

                        getParentModule()->getDisplayString().setTagArg("i", 1, "cyan");
                        ME_data[getParentModule()->getIndex() - cardinalidad_FE].inc_act = 1;

                        incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].mi_id = getParentModule()->getIndex();
                        incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].no_inc = ME_data[getParentModule()->getIndex() - cardinalidad_FE].p;
                        incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].coord_x = mobility->getCurrentPosition().x;
                        incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].coord_y = mobility->getCurrentPosition().y;
                        incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].t_inicio = ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me;
                        //incidentes[p].local = true;
                    }

                    //segregar cada periodo
                    if (((ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me - incs[ME_data[getParentModule()->getIndex() - cardinalidad_FE].index_fail].t_start_inc) % segregar) == 0)
                    {
                        EV_INFO << "alla 4, segregar en tiempo: " << ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me << endl;
                        /////+++++
                        std::ostringstream mi_payload;
                        std::string enti_tipo = std::to_string(1) + "::";
                        std::string mi_id_str = std::to_string(getParentModule()->getIndex()) + ":";
                        std::string no_inc_str = std::to_string(incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].no_inc) + ":";
                        std::string coord_x_str = std::to_string(incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].coord_x) + ":";
                        std::string coord_y_str = std::to_string(incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].coord_y) + ":";
                        std::string t_inicio_str =std::to_string(incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].t_inicio) + "::";
                        std::string incident_edge = traciVehicle->getRoadId().c_str();

                        //inicio cabecera
                        mi_payload << proto_segregation;
                        mi_payload << enti_tipo;
                        //fin cabecera

                        //inicio payload incidente
                        mi_payload << mi_id_str;
                        mi_payload << no_inc_str;
                        mi_payload << coord_x_str;
                        mi_payload << coord_y_str;
                        mi_payload << t_inicio_str;
                        mi_payload << incident_edge;

                        mi_payload << ";";
                        mi_payload << "\0";
                        //fin payload incidente

                        EV_INFO << "mi payload: " << mi_payload.str().data() << endl;

                        auto payload = makeShared<VeinsInetSampleMessage>();
                        payload->setChunkLength(B(pck_size));

                        payload->setRoadId(mi_payload.str().data());
                        timestampPayload(payload);

                        auto packet = createPacket("Segregar !");
                        packet->insertAtBack(payload);
                        sendPacket(std::move(packet));

                        EV_INFO << "Paquete " << getParentModule()->getIndex() << " " << payload << " enviado: " << endl;
                    }
                }
                else
                {
                    if ((ME_data[getParentModule()->getIndex() - cardinalidad_FE].inc_act) && (incs[ME_data[getParentModule()->getIndex() - cardinalidad_FE].index_fail].t_end_inc <= ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me))
                    {
                        coordenada_t_omega = simTime().dbl();

                        getParentModule()->getDisplayString().setTagArg("i", 1, "white");
                        traciVehicle->setSpeed(-1);
                        incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].t_fin = ME_data[getParentModule()->getIndex() - cardinalidad_FE].t_me;
                        incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].delta_t_inc = incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].t_fin - incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].t_inicio;
                        EV_INFO << "alla 5 periodo del incidente: " << incidentes[ME_data[getParentModule()->getIndex() - cardinalidad_FE].p].delta_t_inc << endl;
                        ME_data[getParentModule()->getIndex() - cardinalidad_FE].p++;
                        ME_data[getParentModule()->getIndex() - cardinalidad_FE].inc_act = 0;
                    }
                    EV_INFO << "alla 2 " << endl;
                }
            };
            timerManager.create(veins::TimerSpecification(callback).interval(SimTime(1, SIMTIME_S)));
        }

        else
        {

            auto callback = [this]()
            {
                //if ((inc_activo[designated_me]) && (((t_inic - int(simTime().dbl()) - ) % incremento)) == 0)

                mi_x_actual[getParentModule()->getIndex()] = mobility->getCurrentPosition().x;
                mi_y_actual[getParentModule()->getIndex()] = mobility->getCurrentPosition().y;
                mi_tiempo_actual[getParentModule()->getIndex()] = simTime().dbl();
            };
            timerManager.create(veins::TimerSpecification(callback).interval(SimTime(1, SIMTIME_S)));

            /*if (getParentModule()->getIndex() == (cardinalidad_E - 1))
            {
                int l;
                for (l = 0; l < num_designated_incs; l++)
                {
                    EV_INFO << "preservar: " << endl;
                    if (verbal)
                    {
                        EV_INFO << " " << endl;
                        EV_INFO << "entidad que falla: " << incs[l].designated_me << endl;
                        EV_INFO << "tiempo en que inicia falla: " << incs[l].t_start_inc << endl;
                        EV_INFO << "tiempo en que termina falla: " << incs[l].t_end_inc << endl;
                    }
                }
            }
            EV_INFO << "alla 1: mi id: " << getParentModule()->getIndex() << endl;*/
        }
    }
    return true;
}

bool VeinsInetSampleApplication::stopApplication()
{
    return true;
}

VeinsInetSampleApplication::~VeinsInetSampleApplication()
{
}

void VeinsInetSampleApplication::processPacket(std::shared_ptr<inet::Packet> pk)
{
    auto payload = pk->peekAtFront<VeinsInetSampleMessage>();

    all_data = pk.get()->getCompleteStringRepresentation();

    std::string id_header = "headerLength = ";

    auto header_find = all_data.find(id_header, 0);
    auto header_pos = header_find + std::strlen(id_header.data());
    std::string header = all_data.substr (header_pos,2);
    longitud_header = std::stoul(header);

    if (longitud_payload == 0)
        longitud_payload = std::strlen(payload.get()->str().data());
    else
        longitud_payload = (longitud_payload + std::strlen(payload.get()->str().data())) / 2;

    pck = payload.get()->str();

    EV_INFO << "Paquete recibido: " << payload << endl;
    EV_INFO << "Datos completos del paquete: " << all_data << endl;
    EV_INFO << "carga (payload): " << pck << endl;
    EV_INFO << "longitud encabezado: " << longitud_header << endl;
    EV_INFO << "longitud carga: " << longitud_payload << endl;

    recepciones[getParentModule()->getIndex()]++;

    std::string procesar_payload = payload->getRoadId();
    std::string preambulo;
    std::string origen_str;
    unsigned short origen_num;

    preambulo = procesar_payload.substr(0, 5);
    origen_str = procesar_payload.substr(5, 1);
    origen_num = std::stoi(origen_str, 0, 10);

    EV_INFO << "aculla 1.7 Mi id: " << getParentModule()->getIndex() << ", cadena RX: " << procesar_payload  ;
    EV_INFO << " preambulo: " << preambulo << " y con origen: " << origen_num << endl;

    //requiero discriminar paquetes porque la rsu se recibe a si misma y las entidades moviles reciben a obu incidentada

    if ((getParentModule()->getIndex() < cardinalidad_FE) && (preambulo == proto_segregation)) //entidad fija
    {
        if (FE_data[getParentModule()->getIndex()].first_time)
        {
            FE_data[getParentModule()->getIndex()].t_alpha = simTime().dbl();
            FE_data[getParentModule()->getIndex()].first_time = 0;
            FE_data[getParentModule()->getIndex()].pher_act = 1;
        }
        FE_data[getParentModule()->getIndex()].t_beta = simTime().dbl();
        FE_data[getParentModule()->getIndex()].t_gamma = FE_data[getParentModule()->getIndex()].t_beta + vida_pher;
        FE_data[getParentModule()->getIndex()].countdown_t = vida_pher;
        FE_data[getParentModule()->getIndex()].update_pher = 1;

        mi_payload_pasar[getParentModule()->getIndex()] = procesar_payload; //aqui hago el paso al otro hilo para generar feromona

        EV_INFO << "payload " << getParentModule()->getIndex() << " " << mi_payload_pasar[getParentModule()->getIndex()] << " recibida en el tiempo: " << FE_data[getParentModule()->getIndex()].t_beta << endl;
        EV_INFO << "alfa: " << FE_data[getParentModule()->getIndex()].t_alpha << " beta: " << FE_data[getParentModule()->getIndex()].t_beta << " gama: " << FE_data[getParentModule()->getIndex()].t_gamma << endl;
    }
    else if ((getParentModule()->getIndex() >= cardinalidad_FE) && (preambulo == proto_notification))
    {
        //aqui tengo que discriminar si la entidad que crea el incidente recibe mensaje de feromona sobre el mismo

        int i = 8, j = 0;
        std::string entidad_fija;
        std::string entidad_con_incidente;

        do //obtener la entidad origen
        {
            entidad_fija[j] = procesar_payload[i];
            i++;
            j++;
        }
        while (procesar_payload[i] != ':');
        entidad_fija[j] = '\0';
        feromona_rx.mi_id = std::strtoul(entidad_fija.data(), NULL, 0); //unsigned long
        EV_INFO << "id entidad fija que notifica feromona: " << feromona_rx.mi_id << endl; //recibe el id de la entidad fija

        i++;
        j = 0;
        do //obtener la entidad movil con incidente
        {
            entidad_con_incidente[j] = procesar_payload[i];
            i++;
            j++;
        }
        while (procesar_payload[i] != ':');
        entidad_con_incidente[j] = '\0';
        feromona_rx.id_me = std::strtoul(entidad_con_incidente.data(), NULL, 0); //unsigned long
        EV_INFO << "id entidad movil con incidente: " << feromona_rx.id_me << endl; //recibe el id de la entidad movil con incidente

        if (getParentModule()->getIndex() != feromona_rx.id_me)
        {

            EV_INFO << "feromona consumida " << getParentModule()->getIndex() << " " << procesar_payload << " interpretando datos recibidos " << endl;

            std::string numero_incidente;
            std:: string x_incidente;
            std:: string y_incidente;
            std:: string t_incidente;
            std:: string intensidad1;
            std:: string intensidad2;
            std:: string intensidad3;
            std:: string intensidad4;
            std:: string timer_remaining;
            std:: string edge_inc;

            i++;
            j = 0;
            do //obtener el numero de incidente en entidad incidentada
            {
                numero_incidente[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            numero_incidente[j] = '\0';
            feromona_rx.num_inc_lcl = std::strtoul(numero_incidente.data(), NULL, 0); //unsigned int
            EV_INFO << "numero de incidente en entidad movil incidentada: " << feromona_rx.num_inc_lcl << endl; //numero de incidente en entidad

            i++;
            j = 0;
            do //obtener coordenada x de incidente
            {
                x_incidente[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            x_incidente[j] = '\0';
            feromona_rx.me_coord_x = std::stof(x_incidente.data()); //float
            EV_INFO << "coordenada x de incidente: " << feromona_rx.me_coord_x << endl; //coordenada x de incidente

            i++;
            j = 0;
            do //obtener coordenada y de incidente
            {
                y_incidente[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            y_incidente[j] = '\0';
            feromona_rx.me_coord_y = std::stof(y_incidente.data()); //float
            EV_INFO << "coordenada y de incidente: " << feromona_rx.me_coord_y << endl; //coordenada y de incidente

            i++;
            j = 0;
            do //obtener tiempo de inicio de incidente
            {
                t_incidente[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            t_incidente[j] = '\0';
            feromona_rx.phi_alpha = std::strtoul(t_incidente.data(), NULL, 0); //unsigned long
            EV_INFO << "tiempo de inicio de incidente: " << feromona_rx.phi_alpha << endl; //coordenada y de incidente

            i = i + 2;
            j = 0;
            do //obtener intensidad en azimuth 0
            {
                intensidad1[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            intensidad1[j] = '\0';
            feromona_rx.in01 = std::stof(intensidad1, NULL); //float
            EV_INFO << "intensidad en azimuth 000: " << feromona_rx.in01 << endl; //intensidad azimuth 0

            i++;
            j = 0;
            do //obtener intensidad en azimuth 90
            {
                intensidad2[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            intensidad2[j] = '\0';
            feromona_rx.in02 = std::stof(intensidad2, NULL); //float
            EV_INFO << "intensidad en azimuth 090: " << feromona_rx.in02 << endl; //intensidad azimuth 90

            i++;
            j = 0;
            do //obtener intensidad en azimuth 180
            {
                intensidad3[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            intensidad3[j] = '\0';
            feromona_rx.in03 = std::stof(intensidad3, NULL); //float
            EV_INFO << "intensidad en azimuth 180: " << feromona_rx.in03 << endl; //intensidad azimuth 180

            i++;
            j = 0;
            do //obtener intensidad en azimuth 270
            {
                intensidad4[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            intensidad4[j] = '\0';
            feromona_rx.in04 = std::stof(intensidad4, NULL); //float
            EV_INFO << "intensidad en azimuth 270: " << feromona_rx.in04 << endl; //intensidad azimuth 270

            i = i + 2;
            j = 0;
            do //obtener valor del temporizador
            {
                timer_remaining[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ':');
            timer_remaining[j] = '\0';
            feromona_rx.timer_value = std::strtoul(timer_remaining.data(), NULL, 0); //unsigned int
            EV_INFO << "tiempo de vida restante a la feromona: " << feromona_rx.timer_value << endl; //valor de temporizador

            i = i + 2;
            j = 0;
            do //obtener edge con incidente en version simple
            {
                edge_inc[j] = procesar_payload[i];
                i++;
                j++;
            }
            while (procesar_payload[i] != ';');
            edge_inc[j] = '\0';
            EV_INFO << "edge con incidente: " << edge_inc.data() << endl; //edge con incidente

            //tiempo_rx[getParentModule()->getIndex()] = simTime().dbl();

            if (degradacion)
            {
                std::list<std::string> mi_ruta = traciVehicle->getPlannedRoadIds();
                auto inicio_ruta = mi_ruta.begin();
                auto fin_ruta = mi_ruta.back();
                EV_INFO << "degradacion inicio ruta en: " << *inicio_ruta << " termino ruta en: " << fin_ruta << endl;

                if (std::find(std::begin(mi_ruta), std::end(mi_ruta), edge_inc.data()) != std::end(mi_ruta))
                {
                    desvio[getParentModule()->getIndex()] = 1;

                    if (feromona_rx.timer_value > umbral_desvio)
                    {
                        EV_INFO << "degradacion " << edge_inc.data() << " en mi ruta... deviando.. " << endl;
                        getParentModule()->getDisplayString().setTagArg("i", 1, "blue");
                        traciVehicle->changeRoute(edge_inc.data(), 999.9);
                    }
                    else
                    {
                        //volado
                        unsigned int volado = (rand() % 2);
                        if (volado)
                        {
                            EV_INFO << "degradacion... la probabilidad de que exista el incidente en " << edge_inc.data();
                            EV_INFO << " es menor a umbral en mi ruta... tomo la decision de desviarme " << endl;
                            getParentModule()->getDisplayString().setTagArg("i", 1, "lime");
                            traciVehicle->changeRoute(edge_inc.data(), 999.9);
                        }
                        else
                        {
                            EV_INFO << "degradacion... la probabilidad de que exista el incidente en " << edge_inc.data();
                            EV_INFO << " es menor a umbral en mi ruta... tomo la decision continuar sobre la ruta " << endl;
                            getParentModule()->getDisplayString().setTagArg("i", 1, "olive");
                        }
                    }
                }
                else
                {
                    float current_intensity = (float)feromona_rx.timer_value / vida_pher;
                    EV_INFO << "degradacion " << feromona_rx.timer_value << " " << current_intensity << endl;
                    if ((1 >= current_intensity) && (current_intensity > 0.75))
                        getParentModule()->getDisplayString().setTagArg("i", 1, "red");
                    else if ((0.75 >= current_intensity) && (current_intensity > 0.50))
                        getParentModule()->getDisplayString().setTagArg("i", 1, "orange");
                    else if ((0.50 >= current_intensity) && (current_intensity > 0.25))
                        getParentModule()->getDisplayString().setTagArg("i", 1, "yellow");
                    else
                        getParentModule()->getDisplayString().setTagArg("i", 1, "green");
                }
            }
            else // afectacion solamente
            {
                getParentModule()->getDisplayString().setTagArg("i", 1, "blue");
                traciVehicle->changeRoute(edge_inc.data(), 999.9);
            }
        }
        else
        {
            EV_INFO << "payload " << getParentModule()->getIndex() << " " << procesar_payload << " ignorando dato recibido " << endl;
            payload.reset();
        }

        if (!haveForwarded)
        {
            tiempo_rx[getParentModule()->getIndex()] = simTime().dbl();
            mi_x_rx[getParentModule()->getIndex()] = mobility->getCurrentPosition().x;
            mi_y_rx[getParentModule()->getIndex()] = mobility->getCurrentPosition().y;
            EV_INFO << "mis coordenadas al recibir: " <<  mi_x_rx[getParentModule()->getIndex()] << "," << mi_y_rx[getParentModule()->getIndex()] << endl;
            distancia_manhattan[getParentModule()->getIndex()] = distanciaM (feromona_rx.me_coord_x, feromona_rx.me_coord_y, mi_x_rx[getParentModule()->getIndex()], mi_y_rx[getParentModule()->getIndex()]);
        }

        haveForwarded = true;
    }
    else
    {
        EV_INFO << "payload " << getParentModule()->getIndex() << " " << procesar_payload << " ignorando dato recibido " << endl;
        payload.reset();
    }
    return;
}

