//flooding relay

#include "veins_inet/VeinsInetSampleApplication.h"

#include "inet/common/ModuleAccess.h"
#include "inet/common/packet/Packet.h"
#include "inet/common/TagBase_m.h"
#include "inet/common/TimeTag_m.h"
#include "inet/networklayer/common/L3AddressResolver.h"
#include "inet/networklayer/common/L3AddressTag_m.h"
#include "inet/transportlayer/contract/udp/UdpControlInfo_m.h"

#include "veins_inet/VeinsInetSampleMessage_m.h"

#include <iostream>
#include <fstream>

#define max_t 299
#define t_inic 21
#define t_fin 221
#define incremento 5
#define max_me 500
#define designated_me 5

#define my_file_name "flooding-r.csv"

using namespace inet;

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

unsigned long secuencia_backup;
//---variables metricas a archivo

Define_Module(VeinsInetSampleApplication);

void archivar (int designated)
{
    my_file << "resumen+++" << endl;
    my_file << "id entidad que provoca incidente: " << endl;
    my_file << designated << endl;

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

        if ((rec > designated_me) && (!activado[rec]))
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

VeinsInetSampleApplication::VeinsInetSampleApplication()
{
}

bool VeinsInetSampleApplication::startApplication()
{
    tiempo_inicio[getParentModule()->getIndex()] = simTime().dbl();

    if (getParentModule()->getIndex() == 0)
    {
        my_file.open(my_file_name, std::ios::out);

        auto callback = [this]()
        {
            if ((inc_activo[designated_me]) && (((t_inic - int(simTime().dbl()) + 1) % incremento)) == 0)
            {
                int rec;
                if (rec_backup == 0)
                    rec = 0 + designated_me;
                else
                    rec = rec_backup;

                unsigned long entidades_en_ambiente = 0;
                unsigned long paquetes_recibidos = 0;
                //unsigned long reenvios_ronda = 0;

                my_file << "tiempo actual: " << simTime().dbl() << " ocurrencia numero: " << ocurrencia[designated_me] << endl;
                my_file << "+++ id, habilitado, tiempo inicio operaciones, paquetes recibidos, reenvios, mi x actual, mi y actual, tiempo de coordenadas, si hago desvio: " << endl;
                do
                {
                    my_file << rec << "," << activado[rec] << "," << tiempo_inicio[rec] << "," << recepciones[rec] << "," ;
                    my_file << reenvios[rec] << "," << mi_x_actual[rec] << "," << mi_y_actual[rec] << "," << mi_tiempo_actual[rec] << ",";
                    my_file << desvio[rec] << endl;

                    if ((activado[rec] > 0) && (mi_x_actual[rec] > 0) && (mi_y_actual[rec] > 0))
                        entidades_en_ambiente++;

                    if ((recepciones[rec] > 0) && (activado[rec] > 0))
                        paquetes_recibidos++;

                    //reenvios_ronda = reenvios_ronda + reenvios[rec];

                    rec++;
                }
                while (activado[rec] != 0);

                if (entidades_en_ambiente)
                    rec_backup = rec;

                my_file << "paquetes recibidos, entidades en el ambiente " << endl;
                my_file << paquetes_recibidos << "," << entidades_en_ambiente << endl;

                my_file << endl;
            }

            if (simTime().dbl() > max_t)
            {
                EV_INFO << "terminar " << endl;

                archivar(designated_me);
            }
        };
        timerManager.create(veins::TimerSpecification(callback).interval(SimTime(1, SIMTIME_S)));
    }
    else if (getParentModule()->getIndex() == designated_me)
    {
        inicial[designated_me] = 0;
        inc_activo[designated_me] = 0;

        auto callback = [this]()
        {
            tiempo_rx[designated_me] = simTime().dbl();

            if (((t_inic <= tiempo_rx[designated_me]) && (tiempo_rx[designated_me] <= t_fin)) && (!inicial[designated_me]))
            {
                getParentModule()->getDisplayString().setTagArg("i", 1, "red");
                traciVehicle->setSpeed(0);
                inicial[designated_me] = 1;
                inc_activo[designated_me] = 1;

                coordenada_x = mobility->getCurrentPosition().x;
                coordenada_y = mobility->getCurrentPosition().y;
                coordenada_t_alpha = simTime().dbl();
            }

            if ((inc_activo[designated_me]) && ((t_inic - tiempo_rx[designated_me]) % incremento) == 0)
            {
                std::ostringstream mi_payload;
                std::string mi_id_str = std::to_string(getParentModule()->getIndex()) + ":";//"::";
                std::string secuencia_str = std::to_string(ocurrencia[designated_me]) + "::";
                std::string coord_x_str = std::to_string(coordenada_x) + ":";
                std::string coord_y_str = std::to_string(coordenada_y) + ":";
                std::string t_inicio_str =std::to_string(coordenada_t_alpha) + "::";
                std::string incident_edge = traciVehicle->getRoadId().c_str();

                mi_payload << mi_id_str;
                mi_payload << secuencia_str;
                mi_payload << coord_x_str;
                mi_payload << coord_y_str;
                mi_payload << t_inicio_str;
                mi_payload << incident_edge;

                mi_payload << ";";
                mi_payload << "\0";

                EV_INFO << "mi payload: " << mi_payload.str().data() << endl;

                auto payload = makeShared<VeinsInetSampleMessage>();
                payload->setChunkLength(B(200));

                payload->setRoadId(mi_payload.str().data());
                timestampPayload(payload);

                auto packet = createPacket("accidente");
                packet->insertAtBack(payload);
                sendPacket(std::move(packet));

                ocurrencia[designated_me]++;
            }

            if ((t_fin <= tiempo_rx[designated_me]) && (inc_activo[designated_me]))
            {
                getParentModule()->getDisplayString().setTagArg("i", 1, "white");
                coordenada_t_omega = simTime().dbl();
                traciVehicle->setSpeed(-1);
                inicial[5] = 0;
                inc_activo[5] = 0;
            }
        };
        timerManager.create(veins::TimerSpecification(callback).interval(SimTime(1, SIMTIME_S)));
    }
    else
    {
        activado[getParentModule()->getIndex()] = 1;

        auto callback = [this]()
        {
            //if ((inc_activo[designated_me]) && (((t_inic - int(simTime().dbl()) - ) % incremento)) == 0)
            {
                mi_x_actual[getParentModule()->getIndex()] = mobility->getCurrentPosition().x;
                mi_y_actual[getParentModule()->getIndex()] = mobility->getCurrentPosition().y;
                mi_tiempo_actual[getParentModule()->getIndex()] = simTime().dbl();
            }

        };
        timerManager.create(veins::TimerSpecification(callback).interval(SimTime(1, SIMTIME_S)));
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
    all_data = pk.get()->getCompleteStringRepresentation();

    std::string id_header = "headerLength = ";

    auto header_find = all_data.find(id_header, 0);
    auto header_pos = header_find + std::strlen(id_header.data());
    std::string header = all_data.substr (header_pos,2);
    longitud_header = std::stoul(header);
    auto payload = pk->peekAtFront<VeinsInetSampleMessage>();

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

    int i,j;
    std::string procesar_payload = payload->getRoadId();
    std::string entidad_id;
    std::string secuencia_str;
    unsigned long entidad_id_num, secuencia_num;

    do //obtener la entidad origen
    {
        entidad_id[j] = procesar_payload[i];
        i++;
        j++;
    }
    while (procesar_payload[i] != ':');
    entidad_id[j] = '\0';
    entidad_id_num = std::strtoul(entidad_id.data(), NULL, 0); //unsigned long
    EV_INFO << "id entidad que notifica mensaje: " << entidad_id_num << endl; //recibe el id de la entidad fija

    i++;
    j = 0;
    do //obtener secuencial
    {
        secuencia_str[j] = procesar_payload[i];
        i++;
        j++;
    }
    while (procesar_payload[i] != ':');
    secuencia_str[j] = '\0';
    secuencia_num = std::strtoul(secuencia_str.data(), NULL, 0); //unsigned long
    EV_INFO << "secuencia de mensaje: " << secuencia_num << endl; //recibe el id de la entidad fija

    if (secuencia_num != secuencia_backup)
        haveForwarded = false;

    if ((getParentModule()->getIndex() != entidad_id_num) && (!haveForwarded))
    //if ((getParentModule()->getIndex() != entidad_id_num) && (!haveForwarded) && (secuencia_backup != secuencia_num))
    {

        std::string x_str, y_str, alpha_str;
        float coord_x, coord_y;
        unsigned long alpha;
        std::string edge;

        // procesar payload

        i = i + 2;
        j = 0;
        do //obtener coordenada x de incidente
        {
            x_str[j] = procesar_payload[i];
            i++;
            j++;
        }
        while (procesar_payload[i] != ':');
        x_str[j] = '\0';
        coord_x = std::stod (x_str.data()); //unsigned long
        EV_INFO << "coordenada x de incidente: " << coord_x << endl; //coordenada x de incidente

        i++;
        j = 0;
        do //obtener coordenada y de incidente
        {
            y_str[j] = procesar_payload[i];
            i++;
            j++;
        }
        while (procesar_payload[i] != ':');
        y_str[j] = '\0';
        coord_y = std::stod(y_str.data()); //unsigned long
        EV_INFO << "coordenada y de incidente: " << coord_y << endl; //coordenada y de incidente

        i++;
        j = 0;
        do //obtener tiempo de inicio de incidente
        {
            alpha_str[j] = procesar_payload[i];
            i++;
            j++;
        }
        while (procesar_payload[i] != ':');
        alpha_str[j] = '\0';
        alpha = std::strtoul(alpha_str.data(), NULL, 0); //unsigned long
        EV_INFO << "tiempo de inicio de incidente: " << alpha << endl; //coordenada y de incidente

        i = i + 2;
        j = 0;
        do //obtener edge con incidente en version simple
        {
            edge[j] = procesar_payload[i];
            i++;
            j++;
        }
        while (procesar_payload[i] != ';');
        edge[j] = '\0';
        EV_INFO << "edge con incidente: " << edge.data() << endl; //edge con incidente
        // procesar payload

        mi_x_rx[getParentModule()->getIndex()] = mobility->getCurrentPosition().x;
        mi_y_rx[getParentModule()->getIndex()] = mobility->getCurrentPosition().y;
        EV_INFO << "mis coordenadas al recibir: " <<  mi_x_rx[getParentModule()->getIndex()] << "," << mi_y_rx[getParentModule()->getIndex()] << endl;
        distancia_manhattan[getParentModule()->getIndex()] = distanciaM (coord_x, coord_y, mi_x_rx[getParentModule()->getIndex()], mi_y_rx[getParentModule()->getIndex()]);

        std::list<std::string> mi_ruta = traciVehicle->getPlannedRoadIds();
        auto inicio_ruta = mi_ruta.begin();
        auto fin_ruta = mi_ruta.back();
        EV_INFO << "degradacion inicio ruta en: " << *inicio_ruta << " termino ruta en: " << fin_ruta << endl;

        if (std::find(std::begin(mi_ruta), std::end(mi_ruta), edge.data()) != std::end(mi_ruta))
        {
            desvio[getParentModule()->getIndex()] = 1;
            //if ((secuencia_num % 2) == 0)
                getParentModule()->getDisplayString().setTagArg("i", 1, "yellow");
            /*else
                getParentModule()->getDisplayString().setTagArg("i", 1, "blue");*/
            traciVehicle->changeRoute(edge.data(), 999.9);
        }
        else
        {
            if ((secuencia_num % 2) == 0)
                getParentModule()->getDisplayString().setTagArg("i", 1, "green");
            else
                getParentModule()->getDisplayString().setTagArg("i", 1, "blue");
        }

        //if (haveForwarded) return;

        auto packet = createPacket("relay");
        packet->insertAtBack(payload);
        sendPacket(std::move(packet));

        tiempo_rx[getParentModule()->getIndex()] = simTime().dbl();

        reenvios[getParentModule()->getIndex()]++;
        secuencia_backup = secuencia_num;
        haveForwarded = true;
    }
}
