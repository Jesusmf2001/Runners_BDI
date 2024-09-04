model main

global {
    // Carga de archivos SHP
    file shape_file_buildings <- file("../includes/building.shp");
    file shape_file_roads <- file("../includes/road.shp");
    file shape_file_bounds <- file("../includes/bounds.shp");
    file shape_file_fountains <- file("../includes/fountain.shp");
    geometry shape <- envelope(shape_file_bounds)#m;
    
    // Número de corredores
    int num_runners <- 0;
    int siguiente_id <- 0;
    list<point> localizacion_fuentes <- [];
    list<calle> cortadas <- [];
    float step <- 0.1#s;

    // Predicados globales
    predicate localizacion_fuente <- new_predicate("fuente_en");
    predicate llevo_mochila <- new_predicate("mochila");
    predicate nada <- new_predicate("nada");
    predicate correr <- new_predicate("correr");
    predicate espera <- new_predicate("espera");
    predicate en_casa <- new_predicate("en_casa");
    predicate estoy_en_fuente <- new_predicate("estoy_en_fuente");
    predicate cansado <- new_predicate("cansado");
    predicate tengo_sed <- new_predicate("tengo_sed");
    predicate ir_casa <- new_predicate("ir_casa");
    predicate ir_fuente <- new_predicate("ir_fuente");
    predicate elegir_fuente <- new_predicate("elegir_fuente");
    predicate elegir_punto <- new_predicate("elegir_punto");
    predicate beber_agua <- new_predicate("beber_agua");
    predicate consumir_snack <- new_predicate("consumir_snack");
    graph the_graph;
    
    // Inicialización del modelo y creación de especies
    init {
        // Creación de elementos a partir de shapefiles
        create building from: shape_file_buildings with: [type::string(read("NATURE"))] {
            if type = "Industrial" {
                color <- #lightslategrey;
            }
        }

        create fountain from: shape_file_fountains {
            localizacion_fuentes <+ (self.location);
        }

        create calle from: shape_file_roads;
        the_graph <- as_edge_graph(calle);
        create runner number: num_runners;

	    create runner number: 1 {
		    id <- siguiente_id;
		    siguiente_id <- siguiente_id + 1;
		    // Corredor sin mochila
		    energy <- 5000.0;
		    sed <- 200.0;
		    nivel <- "medio";
		    speed <- 10#km/#h;
		    mi_color <- #blue;
		    do add_belief(nada);
		    mi_casa <- any_location_in(one_of(building));
	        location <- any_location_in(one_of(the_graph.vertices));
		    write "Corredor " + string(id) + " sin mochila creado.";
		}
		
		create runner number: 1 {
		    id <- siguiente_id;
		    siguiente_id <- siguiente_id + 1;
		    // Corredor con mochila
		    energy <- 5000.0;
		    sed <- 200.0;
		    nivel <- "alto";
		    speed <- 12#km/#h;
		    mi_color <- #green;
		    do add_belief(llevo_mochila); // Añadimos la creencia de que lleva mochila
		    agua_mochila <- 300.0; // Definir agua en la mochila
		    snack <- 3; // Definir número de snacks
		    max_agua <- 300.0; // Capacidad máxima de agua en la mochila
		    do add_belief(nada);
		    mi_casa <- any_location_in(one_of(building));
	        location <- any_location_in(one_of(the_graph.vertices));
		    write "Corredor " + string(id) + " con mochila creado. Lleva " + string(agua_mochila) + " ml de agua y " + string(snack) + " snacks.";
		}
	}
    
    // Reflex para averiar una fuente aleatoria
    reflex averiar_fuente {
        bool averiar <- flip(0.0000); 
        if (averiar) {
            fountain fuente_averiada <- one_of(fountain as list);
            ask fuente_averiada {
                color <- #red;
                averiada <- true;
            }
        }
    }
    
    // Reflex para cortar una calle aleatoria
    reflex cortar_calle {
        bool cortar <- flip(0.0000);  
        if (cortar) {
            calle calle_cortada <- one_of(calle as list);
            ask calle_cortada {
                color <- #red;
                cortada <- true;
            }
            the_graph <-  as_edge_graph(calle - cortadas);
        }
    }
}

// Definición del agente Corredor
species runner skills: [moving, fipa] control: simple_bdi {
    int id;
    float speed;          // Velocidad del corredor
    float tiempo_corriendo; // Tiempo total corriendo
    float distancia_recorrida; // Distancia total recorrida
    point mi_casa;         // Localización de la casa del corredor
    point tarj;            // Objetivo actual del corredor
    float energy;          // Energía del corredor
    float sed;             // Nivel de sed del corredor
    point ultimo_punto;    // Última posición
    point proximo_punto;   // Próxima posición
    string nivel;          // Nivel de condición física
    rgb mi_color;          // Color del corredor
    list<runner> amigos;   // Lista de amigos del corredor
    int snack;             // Número de snacks que lleva
    float agua_mochila;    // Cantidad de agua en la mochila
    float max_agua;        // Capacidad máxima de agua en la mochila
    
    reflex bajar_energia when: energy > 0 {
        energy <- energy - 0.01;
        tiempo_corriendo <- tiempo_corriendo + step;
        distancia_recorrida <- distancia_recorrida + (step * speed);
        //write "Corredor " + string(id) + " ha corrido " + string(distancia_recorrida) + " m y tiene " + string(energy) + " de energía.";
        if (energy <= 0) {
            energy <- 0.0;
            speed <- 3.8#km/#h;  
            write "Corredor " + string(id) + " está exhausto. Reduzco velocidad.";
        }
    }
     
    reflex bajar_sed when: sed > 0 {
        sed <- sed - 0.01;
        if (sed <= 0) {
            if (!has_belief(tengo_sed)) {
                do add_belief(tengo_sed);
                write "Corredor " + string(id) + " tiene sed.";
            }
        }
    }
    
    reflex check_energy when: energy < 10.0 {
        if (!has_belief(cansado)) {
            write "Corredor " + string(id) + " está cansado.";
            do add_belief(cansado);
        }
    }
    
    reflex check_energy_ when: energy > 10.0 {
        if (has_belief(cansado)) {
            write "Corredor " + string(id) + " está cansado.";
            do remove_belief(cansado);
        }
    }


    perceive target: fountain in: 10.0 {
        ask myself {
            float min_distance <- 100.0;
            point nearest_fountain_location <- nil;
            fountain nearest_fountain <- nil;

            loop f over: fountain as list {
                float current_distance <- distance_to(f.location, location);

                if (current_distance < min_distance) {
                    min_distance <- current_distance;
                    nearest_fountain_location <- f.location;
                    nearest_fountain <- f;
                }
            }

            if (nearest_fountain != nil) {
                if (nearest_fountain.averiada) {
                    predicate fuente_averiada_belief <- new_predicate("fuente_averiada_en", ["fuente"::nearest_fountain, "location_value"::nearest_fountain_location]);
                    if (!has_belief(fuente_averiada_belief)) {
                        do add_belief(fuente_averiada_belief);
                        write "Corredor " + string(id) + " detectó que la fuente en " + string(nearest_fountain_location) + " está averiada.";
                    }
                } else {
                    predicate nearest_fountain_belief <- new_predicate("fuente_en", ["location_value"::nearest_fountain_location]);
                    if (!has_belief(nearest_fountain_belief)) {
                        do add_belief(nearest_fountain_belief);
                        write "Corredor " + string(id) + " detectó una fuente en " + string(nearest_fountain_location) + ".";
                    }
                }
            }
        }
    }
    
    perceive target: calle in: 10.0 {
        ask myself {
            calle calle_cercana <- nil;
            float min_distance <- 100.0;
            bool cort <- false;
            
            loop r over: calle as list {
                float current_distance <- distance_to(r.location, location);

                if (current_distance < min_distance) {
                    min_distance <- current_distance;
                    calle_cercana <- r;
                }
            }
            
            ask calle_cercana {
                if cortada {
                    cort <- true;
                }
            }
            if (calle_cercana != nil and cort) {
                predicate calle_cortada <- new_predicate("calle_cortada_en", ["vertice1"::calle_cercana.vertice1, "vertice2"::calle_cercana.vertice2]);
                if (!has_belief(calle_cortada)) {
                    do add_belief(calle_cortada);
                    write "Corredor " + string(id) + " detectó que la calle " + string(calle_cercana) + " está cortada.";
                }
            }
        }
    }

    perceive target: runner in: 10.0 { 
        ask runner {
            if (myself in self.amigos) {
                // Compartir información sobre fuentes averiadas
                list sus_averias <- myself.get_beliefs_with_name("fuente_averiada_en");
                list mis_averias <- self.get_beliefs_with_name("fuente_averiada_en");
                loop averia over: sus_averias {
                    predicate predicado_averia <- get_predicate(mental_state(averia));
                    bool exists <- false;

                    loop mi_averia over: mis_averias {
                        predicate predicado_mi_averia <- get_predicate(mental_state(mi_averia));
                        if (predicado_mi_averia = predicado_averia) {
                            exists <- true;
                            break;
                        }
                    }

                    if (!exists) {
                        do add_belief(predicado_averia);
                        write "Corredor " + string(id) + " aprendió sobre la avería en " + string(predicado_averia);
                    }
                }

                // Compartir información sobre calles cortadas
                list sus_calles_cortadas <- myself.get_beliefs_with_name("calle_cortada_en");
                list mis_calles_cortadas <- self.get_beliefs_with_name("calle_cortada_en");
                loop calle_cortada over: sus_calles_cortadas {
                    predicate predicado_calle_cortada <- get_predicate(mental_state(calle_cortada));
                    bool exists <- false;

                    loop mi_calle_cortada over: mis_calles_cortadas {
                        predicate predicado_mi_calle_cortada <- get_predicate(mental_state(mi_calle_cortada));
                        if (predicado_mi_calle_cortada = predicado_calle_cortada) {
                            exists <- true;
                            break;
                        }
                    }

                    if (!exists) {
                        do add_belief(predicado_calle_cortada);
                        write "Corredor " + string(id) + " aprendió sobre la calle cortada en " + string(predicado_calle_cortada);
                    }
                }
            }
        }
    }

    perceive target: runner in: 10.0 when: has_belief(tengo_sed) {
        ask runner {
            // Obtener las creencias de fuente_en del corredor percibido
            list creencias_fuentes <- get_beliefs_with_name("fuente_en");

            // Añadir esas creencias al corredor que pregunta
            loop creencia over: creencias_fuentes {
                predicate predicado_fuente <- get_predicate(mental_state(creencia));
                if (!has_belief(predicado_fuente)) {
                    do add_belief(predicado_fuente);
                    write "Corredor " + string(id) + ": aprendió sobre " + string(predicado_fuente);
                }
            }
        }
    }

    perceive target: runner in: 10.0 when: has_belief(cansado) {
        ask runner {
            if (snack > 0) and (energy < myself.energy) and (self in myself.amigos) {
                snack <- snack - 1;
                myself.snack <- myself.snack + 1;
                write "Corredor " + string(id) + " compartió un snack con " + string(myself.id);
            }
        }
    }
    
    perceive target: runner in: 10.0 when: has_belief(cansado) {
        ask runner {
            if (agua_mochila > 100) and (sed < myself.sed) and (self in myself.amigos) {
                agua_mochila <- agua_mochila - 100;
                myself.sed <- myself.sed + 100;
                write "Corredor " + string(id) + " compartió agua con " + string(myself.id);
            }
        }
    }

    plan elegir_punto intention: elegir_punto instantaneous: true {
        list<point> posibles_puntos <- the_graph neighbors_of(location) where (each != ultimo_punto);
        if (!empty(posibles_puntos)) {
            ultimo_punto <- location;
            proximo_punto <- one_of(posibles_puntos);
        } else {
            proximo_punto <- ultimo_punto;  // Si no hay puntos posibles, volver al último punto
        }

        do remove_desire(elegir_punto);
        do remove_intention(elegir_punto, true);
    }

    plan correr intention: correr {
        if (proximo_punto = nil) {
            do add_subintention(get_current_intention(), elegir_punto, true);
            do current_intention_on_hold();
        } else {
            do goto target: proximo_punto on: the_graph;
            if (location = proximo_punto) {
                proximo_punto <- nil;
                do remove_desire(correr);
                do remove_intention(correr);
            }
        }
    }
    
    plan elegir_fuente intention: elegir_fuente instantaneous: true {
        list<point> fuentes_conocidas <- get_beliefs_with_name("fuente_en") collect (point(get_predicate(mental_state(each)).values["location_value"]));
        list<point> fuentes_averiadas <- get_beliefs_with_name("fuente_averiada_en") collect (point(get_predicate(mental_state(each)).values["location_value"]));

        // Filtrar las fuentes conocidas para eliminar las que están averiadas
        fuentes_conocidas <- fuentes_conocidas - fuentes_averiadas;
        
        // Seleccionar la fuente más cercana
        if (!empty(fuentes_conocidas)) {
            tarj <- (fuentes_conocidas with_min_of (each distance_to self));
            write "Corredor " + string(id) + " eligió la fuente en " + string(tarj);
        } else {
            write "Corredor " + string(id) + " no encontró una fuente disponible.";
        }
        
        // Eliminar la intención y el deseo de elegir fuente
        do remove_intention(elegir_fuente, true);
        do remove_desire(elegir_fuente);
    }

    plan ir_fuente intention: ir_fuente {
        if (tarj = nil) {
            do add_subintention(get_current_intention(), elegir_fuente, true);
            do current_intention_on_hold();
            write "Corredor " + string(id) + " no tiene un objetivo de fuente, eligiendo una.";
        } else {
            do goto target: tarj on: the_graph;
            if (location = tarj.location) {
                do remove_desire(ir_fuente);
                do remove_intention(ir_fuente);
                do add_belief(estoy_en_fuente);
                tarj <- nil;
                write "Corredor " + string(id) + " llegó a la fuente.";
            }
        }
    }

    plan ir_casa intention: ir_casa {
        tarj <- mi_casa;
        do goto target: tarj on: the_graph;
        if (location = tarj.location) {
            do add_belief(en_casa);
            do remove_desire(ir_casa);
            do remove_intention(ir_casa);
        }
    }
    
    plan beber_agua intention: beber_agua {
        if !(has_belief(estoy_en_fuente)) {
            if agua_mochila > 100 {
                sed <- sed + 100;
                agua_mochila <- agua_mochila - 100;
                write "Corredor " + string(id) + " bebió agua de la mochila. Sed: " + string(sed);
            } else {
                sed <- sed + agua_mochila;
                agua_mochila <- 0.0;
            }
        } else {
            sed <- 850.0;
            if has_belief(llevo_mochila) {
                agua_mochila <- max_agua;
                write "Corredor " + string(id) + " bebió agua en la fuente y rellenó la mochila.";
            }else{
            	write "Corredor " + string(id) + " bebió agua en la fuente";
            }
            
        }
        
        do add_intention(espera);
        do remove_belief(tengo_sed);
        do remove_belief(estoy_en_fuente);
        do remove_intention(beber_agua);
        do remove_desire(beber_agua);
    }
    
    plan espera intention: espera {
        write "Corredor " + string(id) + " está bebiendo agua.";
        loop times: 60 {
            // Simular la espera
        }
        do remove_intention(espera);
        do remove_desire(espera);
    }
    
    plan consumir_snack intention: consumir_snack {
        snack <- snack - 1;
        energy <- energy + 100;
        write "Corredor " + string(id) + " consumió un snack. Energía: " + string(energy);
        do remove_intention(consumir_snack);
        do remove_desire(consumir_snack);
    }

    // Reglas de deseos e intenciones
    rule belief: nada new_desire: correr strength: 1.0;
    rule belief: cansado new_desire: ir_casa strength: 11.0;
    rule belief: tengo_sed when: !has_belief(llevo_mochila) new_desire: ir_fuente strength: 11.0;
    rule beliefs: [tengo_sed, estoy_en_fuente] new_desire: beber_agua strength: 20.0;
    rule beliefs: [tengo_sed, llevo_mochila] when: agua_mochila > 0 new_desire: beber_agua strength: 11.0;
    rule belief: cansado when: snack > 0 new_desire: consumir_snack strength: 15.0;
	rule belief: cansado when: tiempo_corriendo > (3600/step) strength: 20.0;
    aspect default {
        draw circle(10) color: mi_color border: #black;
    }
}
species building {
    string type;
    rgb color <- #gray;

    aspect base {
        draw shape color: color;
    }
}

species calle {
    rgb color <- #black;
    bool cortada <- false;
    point vertice1;
    point vertice2;

    init {
        list<point> vertices <- points(shape); 
        vertice1 <- first(vertices);  // Primer vértice
        vertice2 <- last(vertices);  // Último vértice
    }
    
    reflex cortar when: cortada and !(self in cortadas) {
        cortadas <- cortadas + self;
    }
    
    aspect base {
        draw shape color: color;
    }
}


species fountain {
    rgb color <- #blue;
    bool averiada <- false;

    aspect base {
        draw circle(5) color: color;
    }
}

experiment runners_simulation type: gui {
    parameter "Shapefile for the buildings:" var: shape_file_buildings category: "GIS";
    parameter "Shapefile for the roads:" var: shape_file_roads category: "GIS";
    parameter "Shapefile for the bounds:" var: shape_file_bounds category: "GIS";
    parameter "Shapefile for the fountains:" var: shape_file_fountains category: "GIS";

    output {
        display city_display type: 2d {
            species building aspect: base;
            species calle aspect: base;
            species fountain aspect: base;
            species runner;
        }
        
        monitor "Number of fountains" value: length(fountain as list);
    }
}