model main

global {
    // Carga de archivos SHP
    file shape_file_buildings <- file("../includes/building.shp");
    file shape_file_roads <- file("../includes/road.shp");
    file shape_file_bounds <- file("../includes/bounds.shp");
    file shape_file_fountains <- file("../includes/fountain.shp");
    geometry shape <- envelope(shape_file_bounds)#m;
    
    // Número de corredores
    int num_runners <- 10;
    int siguiente_id <- 0;
    list<point> localizacion_fuentes <- [];
    list<calle> cortadas <- [];
    float step <- 10#s;

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
    }
    
    // Reflex para averiar una fuente aleatoria
    reflex averiar_fuente {
        bool averiar <- flip(0.00001); 
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
        bool cortar <- flip(0.00001);  
        if (cortar) {
            calle calle_cortada <- one_of(calle as list);
            ask calle_cortada {
                color <- #red;
                cortada <- true;
            }
            the_graph <-  as_edge_graph(calle - cortadas);
        }
    }
    
    reflex terminar_simulacion when: empty(runner where !each.has_belief(en_casa)){
    	do pause;
    	ask runner{
    		write string(id) + " ha corrido " + distancia_recorrida/1000 + "km, en un total de " + tiempo_corriendo/60 + " minutos.";
    	}
    	}
}

// Definición del agente Corredor
species runner skills: [moving, fipa] control: simple_bdi {
    int id;
    float speed <- 0.35#m/#h;
    float tiempo_corriendo <- 0.0#s;
    float distancia_recorrida <- 0.0#m;
    point mi_casa;
    point tarj;
    float energy;
    float sed;
    point ultimo_punto;
    point proximo_punto;
    string nivel;
    rgb mi_color;
    list<runner> amigos <- [];
    int snack <- 0;
    float agua_mochila <- 0.0;
    float max_agua <- 0.0;
    float meta <- 0.0#s;
    
    init {
        id <- siguiente_id;
        siguiente_id <- siguiente_id + 1;
        int nivel_choice <- rnd(2);
        if (nivel_choice = 0) {
            nivel <- "bajo";
            speed <- 8#km/#h;
            energy <- 125.0;
            mi_color <- #yellow;
            meta <- 40*60#s;
        } else if (nivel_choice = 1) {
            nivel <- "medio";
            speed <- 10#km/#h;
            energy <- 150.0;
            mi_color <- #orange;
            meta <- 50*60#s;
        } else if (nivel_choice = 2) {
            nivel <- "alto";
            speed <- 12#km/#h;
            energy <- 200.0;
            mi_color <- #red;
            meta <- 3600#s;
        }
        
        list<runner> corredores <- runner as list;
        corredores <- corredores - self;
        
        loop corredor over: corredores {
            if  (not (corredor in amigos)) and flip(0.5) {
                amigos <- amigos + corredor;
                ask corredor {
                    self.amigos <- self.amigos + myself;
                }
            }
        }
        
        sed <- 500.0;
        mi_casa <- any_location_in(one_of(building));
        location <- any_location_in(one_of(the_graph.vertices));
        do add_belief(nada);
        
        bool mochila <- flip(0.5);
        if mochila and nivel_choice = 2 {
            do add_belief(llevo_mochila);
        }
        if has_belief(llevo_mochila) {
            snack <- rnd(1,5);
            agua_mochila <- rnd(100.0,300.0);
            max_agua <- agua_mochila;
        }
    }
    
        reflex bajar_energia when: energy > 0 and !has_belief(en_casa) {
        energy <- energy - (0.01*step);
        tiempo_corriendo <- tiempo_corriendo + step;
        distancia_recorrida <- distancia_recorrida + (step * speed);
        if (energy <= 0) {
            energy <- 0.0;
            speed <- 3.8#km/#h;  
        }
    }
     
    reflex bajar_sed when: sed > 0 {
        sed <- sed - 0.01;
        if (sed <= 0) {
            if (!has_belief(tengo_sed)) {
                do add_belief(tengo_sed);
            }
        }
        if (sed > 75.0) and has_belief(tengo_sed){
        	do remove_belief(tengo_sed);
        }
    }
    
    reflex check_energy when: energy < 10.0 {
        if (!has_belief(cansado)) and (!has_belief(en_casa)) {
            do add_belief(cansado);
        }
    }
    
    reflex check_energy_ when: energy > 10.0 {
        if (has_belief(cansado)) {
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
                    }
                } else {
                    predicate nearest_fountain_belief <- new_predicate("fuente_en", ["location_value"::nearest_fountain_location]);
                    if (!has_belief(nearest_fountain_belief)) {
                        do add_belief(nearest_fountain_belief);
                    }
                }
            }
        }
    }
    
    perceive target: calle in: 20.0 {
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
                }
            }
        }
    }

    perceive target: runner in: 10.0 when: has_belief(cansado) and snack = 0 {
        if (snack > 0) and (energy > myself.energy) and (self in myself.amigos) {
            snack <- snack - 1;
            myself.snack <- myself.snack + 1;
        }
	}
    
    perceive target: runner in: 10.0 when: has_belief(tengo_sed) {
            if (agua_mochila > 100) and (sed > myself.sed) and (self in myself.amigos) {
                agua_mochila <- agua_mochila - 100;
                myself.sed <- myself.sed + 100;
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
                do remove_intention(correr,true);
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
        } 
        
        // Eliminar la intención y el deseo de elegir fuente
        do remove_intention(elegir_fuente, true);
        }

    plan ir_fuente intention: ir_fuente {
        if (tarj = nil) {
            do add_subintention(get_current_intention(), elegir_fuente, true);
            do current_intention_on_hold();
        } else {
            do goto target: tarj on: the_graph;
            if (location = tarj.location) {
                do remove_intention(ir_fuente,true);
                do add_belief(estoy_en_fuente);
                tarj <- nil;
            }
        }
    }

    plan ir_casa intention: ir_casa {
        tarj <- mi_casa;
        do goto target: tarj on: the_graph;
        if (location = tarj.location) {
            do add_belief(en_casa);
            do remove_intention(ir_casa,true);
            do remove_belief(cansado);
            do add_intention(new_predicate("descansar"),100.0);
        }
    }
    
    plan descansar intention: new_predicate("descansar"){
    	
    }
    
    plan beber_agua intention: beber_agua {
        if !(has_belief(estoy_en_fuente)) {
            if agua_mochila > 100 {
                sed <- sed + 100;
                agua_mochila <- agua_mochila - 100;
            } else {
                sed <- sed + agua_mochila;
                agua_mochila <- 0.0;
            }
        } else {
            sed <- 850.0;
            if has_belief(llevo_mochila) {
                agua_mochila <- max_agua;
            }
        }
        
        do add_intention(espera);
        do remove_belief(tengo_sed);
        do remove_belief(estoy_en_fuente);
        do remove_intention(beber_agua,true);
    }
    
    plan espera intention: espera {
        loop times: 60 {
            // Simular la espera
        }
        do remove_intention(espera,true);
    }
    
    plan consumir_snack intention: consumir_snack {
        snack <- snack - 1;
        energy <- energy + 100;
        do remove_intention(consumir_snack,true);
    }

    // Reglas de deseos e intenciones
    rule belief: nada new_desire: correr strength: 1.0;
    rule belief: cansado new_desire: ir_casa strength: 10.0;
    rule belief: tengo_sed when: !has_belief(llevo_mochila) new_desire: ir_fuente strength: 9.0;
    rule beliefs: [tengo_sed, estoy_en_fuente] new_desire: beber_agua strength: 20.0;
    rule beliefs: [tengo_sed, llevo_mochila] when: agua_mochila > 0 new_desire: beber_agua strength: 20.0;
    rule belief: cansado when: snack > 0 new_desire: consumir_snack strength: 15.0;
	rule belief: nada when: tiempo_corriendo > meta new_desire:ir_casa strength: 50.0;
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
