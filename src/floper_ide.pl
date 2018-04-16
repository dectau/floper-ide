
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                  %%
%% LIBRERÍAS                                                        %%
%%                                                                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Cargar librerías XPCE
:- use_module(library(pce)).
:- use_module(library(pce_style_item)).
:- use_module(library(sgml)).
:- pce_autoload(toc_window, library(pce_toc)).
:- pce_autoload(report_dialog, library(pce_report)).
:- pce_autoload(tool_bar, library(toolbar)).
:- pce_autoload(finder, library(find_file)).
:- pce_global(@finder, new(finder)).

% Cargar FLOPER
:- consult('floper.pl').
:- consult('xpce-floper-trees.pl').



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                  %%
%% RECURSOS                                                         %%
%%                                                                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Establecer directorio
:- pce_image_directory('img/').

% Cargar imágenes
resource(img_save, image, image('save.xpm')).
resource(img_saveas, image, image('saveas.xpm')).
resource(img_newproject, image, image('newproject.xpm')).
resource(img_openproject, image, image('openproject.xpm')).
resource(img_newfplfile, image, image('newfplfile.xpm')).
resource(img_openfplfile, image, image('openfplfile.xpm')).
resource(img_newplfile, image, image('newplfile.xpm')).
resource(img_openplfile, image, image('openplfile.xpm')).
resource(img_newscriptfile, image, image('newscriptfile.xpm')).
resource(img_openscriptfile, image, image('openscriptfile.xpm')).
resource(img_run, image, image('run.xpm')).
resource(img_leaves, image, image('leaves.xpm')).
resource(img_tree, image, image('tree.xpm')).
resource(img_showrules, image, image('showrules.xpm')).
resource(img_unfold, image, image('unfold.xpm')).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                  %%
%% PREDICADOS DINÁMICOS                                             %%
%%                                                                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic
	floper_edditing_file/1.

floper_edditing_file(empty).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                  %%
%% JERARQUÍA DE DIRECTORIO                                          %%
%%                                                                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pce_begin_class(directory_hierarchy, toc_window, "Jerarquía de directorio").

initialise(FB, Root:directory) :->
	send(FB, send_super, initialise),
	get(Root, name, Name),
	(Name == empty ; send(FB, root, toc_folder(Name, Root))).

expand_node(FB, D:directory) :->
	new(SubDirsNames, chain),
	new(FileNames, chain),
	send(D, scan, FileNames, SubDirsNames),
	get(SubDirsNames, map, ?(D, directory, @arg1), SubDirs),
	send(SubDirs, for_all, message(FB, son, D, create(toc_folder, @arg1?name, @arg1))),
	get(FileNames, map, ?(D, file, @arg1), SubFiles),
	send(SubFiles, for_all, message(FB, son, D, create(toc_file, @arg1?base_name, @arg1))).        

open_node(FB, Node:file) :->
	send(FB?frame, edit_file, Node).
		
reload(FB, Root:directory) :->
	get(Root, name, Name),
	send(FB, root, toc_folder(Name, Root)).

:- pce_end_class.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                  %%
%% CONSOLA                                                          %%
%%                                                                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pce_begin_class(console, view, "Consola").

initialise(_console) :->
	send_super(_console, initialise),
	send(_console, editable, @off),
	send(_console, label, 'Console'),
	send(_console, font, font(screen, normal, 12)),
	send(_console?text_cursor, displayed, @off).
	
% Insertar texto al final.
append(_console, Text) :->
	get(_console, text_buffer, _text_buffer),
	get(_text_buffer, length, Length),
	send(_console, caret, Length),
	send(_console, insert, Text).
	
% Construir fichero build.xml de un proyecto.
build(_console, File) :->
	send(_console, append, "Building project...\n"),
	file_directory_name(File, Directory),
	working_directory(_, Directory),
	(
		load_structure(File, [element(proyect, XML, _)|_], []),
		send(_console, append, "    Success parsing build.xml file from \""),
		send(_console, append, Directory),
		send(_console, append, "\"\n"),
		(
			member(name=Name, XML),
			send(_console, append, "Loading lattice file of \""),
			send(_console, append, Name),
			send(_console, append, "\" project...\n")
		;
			send(_console, append, "Loading lattice file of the project...\n")
		),
		(
			member(lattice=LAT, XML),
			send(_console, append, "    Lattice \""),
			send(_console, append, LAT),
			send(_console, append, "\" specified\n"),
			string_concat("lat/", LAT, LAT_PATH),
			(
				exists_file(LAT_PATH),
				send(_console, append, "    Lattice \""),
				send(_console, append, LAT),
				send(_console, append, "\" file founded\n"),
				(
					lat(LAT_PATH),
					send(_console, append, "    Lattice \""),
					send(_console, append, LAT),
					send(_console, append, "\" file loaded correctly\n")
				;
					send(_console, append, "    Lattice \""),
					send(_console, append, LAT),
					send(_console, append, "\" file could not be loaded\n")
				)
			;
				send(_console, append, "    Lattice \""),
				send(_console, append, LAT),
				send(_console, append, "\" file not founded\n")
			)
		;
			send(_console, append, "    The lattice filewas not specified\n")
		),
		(
			member(name=Name, XML),
			send(_console, append, "Loading similarities file of \""),
			send(_console, append, Name),
			send(_console, append, "\" project...\n")
		;
			send(_console, append, "Loading similarities file of the project...\n")
		),
		(
			member(similarities=SIM, XML),
			string_length(SIM, SIM_LEN),
			SIM_LEN > 0,
			send(_console, append, "    Similarities \""),
			send(_console, append, SIM),
			send(_console, append, "\" file specified\n"),
			string_concat("sim/", SIM, SIM_PATH),
			(
				exists_file(SIM_PATH),
				send(_console, append, "    Similarities \""),
				send(_console, append, SIM),
				send(_console, append, "\" file founded\n"),
				(
					sim(SIM_PATH),
					send(_console, append, "    Similarities \""),
					send(_console, append, SIM),
					send(_console, append, "\" file loaded correctly\n")
				;
					send(_console, append, "    Similarities \""),
					send(_console, append, SIM),
					send(_console, append, "\" file could not be loaded\n")
				)
			;
				send(_console, append, "    Similarities \""),
				send(_console, append, SIM),
				send(_console, append, "\" file not founded\n")
			)
		;
			send(_console, append, "    Similarities file was not specified\n")
		),
		(
			member(name=Name, XML),
			send(_console, append, "Loading main fuzzy-prolog file of \""),
			send(_console, append, Name),
			send(_console, append, "\" project...\n")
		;
			send(_console, append, "Loading main fuzzy-prolog file of the project...\n")
		),
		(
			member(main=FUZZY, XML),
			send(_console, append, "    Main fuzzy-prolog \""),
			send(_console, append, FUZZY),
			send(_console, append, "\" file specified\n"),
			string_concat("fuzzy/", FUZZY, FUZZY_PATH),
			(
				exists_file(FUZZY_PATH),
				send(_console, append, "    Main fuzzy-prolog \""),
				send(_console, append, FUZZY),
				send(_console, append, "\" file founded\n"),
				(
					parse(FUZZY_PATH),
					send(_console, append, "    Main fuzzy-prolog \""),
					send(_console, append, FUZZY),
					send(_console, append, "\" file loaded correctly\n")
				;
					send(_console, append, "    Main fuzzy-prolog \""),
					send(_console, append, FUZZY),
					send(_console, append, "\" file could not be loaded\n")
				)
			;
				send(_console, append, "    Main fuzzy-prolog \""),
				send(_console, append, FUZZY),
				send(_console, append, "\" file not founded\n")
			)
		;
			send(_console, append, "    Main fuzzy-prolog file was not specified\n")
		)
	;
		send(_console, append, "    Error parsing build.xml file from \""),
		send(_console, append, Directory),
		send(_console, append, "\"\n")
	),
	send(_console, append, "\n").

% Árbol.
tree(_console, Goal) :->
	send(_console, append, "?- intro(\""),
	send(_console, append, Goal),
	send(_console, append, "\"), tree.\n"),
	(
		catch(
			(intro(Goal),
			with_output_to(codes(Tree), tree),
			atom_chars(Tree_print, Tree),
			send(_console, append, Tree_print),
			send(_console, append, "\n"),
			(
				Tree_print == "There is no solution.",
				send(_console, append, "\n")
			;
				true
			)
		), _, send(_console, append, "Syntax error.\n\n"))
	;
		send(_console, append, "Syntax error.\n\n")
	).
	
% Hojas.
leaves(_console, Goal) :->
	send(_console, append, "?- intro(\""),
	send(_console, append, Goal),
	send(_console, append, "\"), leaves."),
	(
		catch(
			(intro(Goal),
			with_output_to(codes(Leaves), leaves),
			atom_chars(Leaves_print, Leaves),
			send(_console, append, Leaves_print),
			send(_console, append, "\n")
		), _, send(_console, append, "\nSyntax error.\n\n"))
	;
		send(_console, append, "\nSyntax error.\n\n")
	).
	
% Ejecutar.
run(_console, Goal) :->
	send(_console, append, "?- intro(\""),
	send(_console, append, Goal),
	send(_console, append, "\"), run.\n"),
	(
		catch(
			(intro(Goal),
			with_output_to(codes(Run), run),
			atom_chars(Run_print, Run),
			send(_console, append, Run_print),
			send(_console, append, "\n"),
			(
				Run_print == "There is no solution.",
				send(_console, append, "\n")
			;
				true
			)
		), _, send(_console, append, "Syntax error.\n\n"))
	;
		send(_console, append, "Syntax error.\n\n")
	).
	
% Mostrar reglas actuales.
show_current_rules(_console) :->
	send(_console, append, "?- show_rules(current).\n"),
	with_output_to(codes(Show), show_rules(current)),
	atom_chars(Show_print, Show),
	send(_console, append, Show_print),
	send(_console, append, "\n").

:- pce_end_class(console).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                  %%
%% VENTANA PRINCIPAL DEL ENTORNO                                    %%
%%                                                                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pce_begin_class(floper, frame, "Ventana principal del entorno").

initialise(_frame) :->
	send_super(_frame, initialise, "FLOPER IDE"),
	send(_frame, background, "#efefef"),
	send(_frame, append, new(_dialog, dialog)),
	send(_dialog, pen, 0),
	send(_dialog, gap, size(5, 5)),
	send(_dialog, append, new(menu_bar)),
	send(_dialog, append, new(tool_bar(_frame))),
	send(_dialog, append, new(tool_bar(_frame))),
	send(_dialog, background, "#efefef"),
	new(_hierarchy, directory_hierarchy(empty)),
	new(_editor, view),
	new(_console, console),
	send(_editor, right, _hierarchy),
	send(_editor, font, font(screen, normal, 12)),
	send(_editor, label, ' '),
	send(_editor, background, '#fafafa'),
	send(_editor, editable, @off),
	send(_editor?text_cursor, displayed, @off),
	send(_hierarchy, width, 200),
	send(_hierarchy, below, _dialog),
	send(_hierarchy, label, 'Project'),
	send(_console, below, _hierarchy),
	send(_console?text_cursor, displayed, @off),
	send(_frame, fill_menu_bar),
	send(_frame, fill_tool_bar).

% Rellenar barra de menús.
fill_menu_bar(_frame) :->
	get(_frame, member, dialog, _dialog),
	get(_dialog, member, menu_bar, _menu_bar),
	get(_frame, member, view, _editor),
	send_list(_menu_bar, append, [
		new(_file, popup("File")),
		new(_edit, popup("Edit")),
		new(_code, popup("Code")),
		new(_run, popup("Run")),
		new(_transformations, popup("Transformations")),
		new(_options, popup("Options")),
		new(_help, popup("Help"))
	]),
	send_list(_file, append, [
		menu_item("New project...", message(_frame, new_project)),
		menu_item("Open project...", message(_frame, open_project)),
		menu_item("Close project", message(_frame, create_project), end_group := @on),
		menu_item("Create Fuzzy-Prolog File in Project...", message(_frame, create_fuzzy_prolog_file_in_project)),
		menu_item("Add Fuzzy-Prolog File to Project...", message(_frame, add_fuzzy_prolog_file_to_project), end_group := @on),
		menu_item("Create Prolog File in Project...", message(_frame, create_prolog_file_in_project)),
		menu_item("Add Prolog File to Project...", message(_frame, add_prolog_file_to_project), end_group := @on),
		menu_item("New Sim File...", message(_frame, new_sim_file)),
		menu_item("Open Sim File...", message(_frame, open_sim_file), end_group := @on),
		menu_item("Create Script File in Project...", message(_frame, create_script_file_in_project)),
		menu_item("Add Script File to Project...", message(_frame, add_script_file_to_project), end_group := @on),
		menu_item("Replace Lattice File in Project...", message(_frame, replace_lattice_file_in_project), end_group := @on),
		menu_item("Save All", message(_frame, save_all)),
		menu_item("Save", message(_frame, save)),
		menu_item("Save As...", message(_frame, save_as), end_group := @on),
		menu_item("Open .txt Tree...", message(_frame, open_txt_tree)),
		menu_item("Open .xml Tree...", message(_frame, open_xml_tree), end_group := @on),
		menu_item("Exit", message(_frame, exit))
	]),
	send_list(_edit, append, [
		menu_item("Undo         (Ctrl+Z)", message(_editor, undo), end_group := @on),
		%menu_item("Redo", message(_editor, redo), end_group := @on),
		menu_item("Cut           (Ctrl+X)", message(_editor, cut)),
		menu_item("Copy         (Ctrl+C)", message(_editor, copy)),
		menu_item("Paste        (Ctrl+V)", message(_editor, paste), end_group := @on),
		menu_item("Select All   (Ctrl+A)", message(_editor, mark_whole_buffer))
	]),
	send_list(_code, append, [
		menu_item("List High-Level Prolog Code", message(_frame, list_high_level_prolog_code)),
		menu_item("Save High-Level Prolog Code...", message(_frame, save_high_level_prolog_code), end_group := @on),
		menu_item("List Low-Level Prolog Code", message(_frame, list_low_level_prolog_code)),
		menu_item("Save Low-Level Prolog Code...", message(_frame, save_low_level_prolog_code), end_group := @on),
		menu_item("Show Project Fuzzy-Prolog Code", message(_frame, show_project_fuzzy_prolog_code)),
		menu_item("Show Project Prolog Code", message(_frame, show_project_prolog_code), end_group := @on),
		menu_item("Show Lattice", message(_frame, show_lattice))
	]),
	send_list(_run, append, [
		menu_item("Execute Goal...", message(_frame, goal, run)),
		menu_item("Execute Script...", message(_frame, execute_script)),
		menu_item("Generate Partial Execution Tree...", message(_frame, goal, tree)),
		menu_item("Generate Leaves...", message(_frame, goal, leaves))
	]),
	send_list(_transformations, append, [
		menu_item("Partial Evaluation", message(_frame, partial_evaluation)),
		menu_item("Fold Transformations...", message(_frame, fold_transformations)),
		menu_item("Unfold Transformations...", message(_frame, unfold_transformations)),
		menu_item("Reductants Calcs", message(_frame, reductants_calcs))
	]),
	send_list(_options, append, [
		menu_item("Change Max Tree Depth...", message(_frame, change_max_tree_depth)),
		menu_item("Change Interpretative Step Mode...", message(_frame, change_interpretative_step_mode))
	]),
	send_list(_help, append, [
		menu_item("User Manual", message(_frame, user_manual)),
		menu_item("About", message(_frame, about))
	]),
	send(_editor, key_binding, '\\C-a', message(_editor, mark_whole_buffer)).

% Rellenar barra de herramientas.
fill_tool_bar(_frame) :->
	get(_frame, member, dialog, _dialog),
	get(_frame, member, console, _console),
	get(_dialog, member, tool_bar, _tool_bar),
	new(@img_save, image('save.xpm')),
	new(@img_saveas, image('saveas.xpm')),
	new(@img_newproject, image('newproject.xpm')),
	new(@img_openproject, image('openproject.xpm')),
	new(@img_newfplfile, image('newfplfile.xpm')),
	new(@img_openfplfile, image('openfplfile.xpm')),
	new(@img_newplfile, image('newplfile.xpm')),
	new(@img_openplfile, image('openplfile.xpm')),
	new(@img_newscriptfile, image('newscriptfile.xpm')),
	new(@img_openscriptfile, image('openscriptfile.xpm')),
	new(@img_run, image('run.xpm')),
	new(@img_leaves, image('leaves.xpm')),
	new(@img_tree, image('tree.xpm')),
	new(@img_showrules, image('showrules.xpm')),
	new(@img_transformations, image('unfold.xpm')),
	send_list(_tool_bar, append, [
		tool_button(save, @img_save, "Save"), gap,
		tool_button(save_as, @img_saveas, "Save As..."), gap, gap, gap,
		tool_button(new_project, @img_newproject, "New Project..."), gap,
		tool_button(open_project, @img_openproject, "Open Project..."), gap, gap, gap,
		tool_button(create_fuzzy_prolog_file_in_project, @img_newfplfile, "Create Fuzzy-Prolog File in Project..."), gap,
		tool_button(add_fuzzy_prolog_file_to_project, @img_openfplfile, "Add Fuzzy-Prolog File to Project..."), gap,
		tool_button(create_prolog_file_in_project, @img_newplfile, "Create Prolog File in Project..."), gap,
		tool_button(add_prolog_file_to_project, @img_openplfile, "Add Prolog File to Project..."), gap,
		tool_button(create_script_file_in_project, @img_newscriptfile, "Create Script File in Project..."), gap,
		tool_button(add_script_file_to_project, @img_openscriptfile, "Add Script File to Project..."), gap, gap, gap,
		tool_button(message(_frame, goal, run), @img_run, "Run..."), gap,
		tool_button(message(_frame, goal, leaves), @img_leaves, "Leaves..."), gap,
		tool_button(message(_frame, goal, tree), @img_tree, "Generate Partial Execution Tree..."), gap, gap, gap,
		tool_button(message(_console, show_current_rules), @img_showrules, "Show current rules"), gap,
		tool_button(unfold_transformations, @img_transformations, "Unfold Transformations...")
	]).
	
% Abrir proyecto.
open_project(_frame) :->
	fasiller_default,
	get(@finder, file, @on, xml, File),
	get(_frame, member, console, _console),
	file_directory_name(File, Directory),
	get(_frame, member, directory_hierarchy, _hierarchy),
	send(_console, build, File),
	send(_hierarchy, reload(Directory)).
	
% Guardar fichero.
save(_frame) :->
	get(_frame, member, view, _editor),
	floper_edditing_file(Path),
	delete_file(Path),
	send(_editor, save, Path),
	file_base_name(Path, Name),
	send(_editor, label, Name).

% Editar fichero.
edit_file(_frame, _node) :->
	get(_frame, member, view, _editor),
	send(_editor, load, _node),
	send(_editor, editable, @on),
	get(_node, name, Path),
	file_base_name(Path, Name),
	send(_editor, label, Name),
	send(_editor, background, '#ffffff'),
	send(_editor?text_cursor, displayed, @on),
	retract(floper_edditing_file(_)),
	assertz(floper_edditing_file(Path)).
	
% Ejecutar objetivo.
goal(_frame, Method) :->
	get(_frame, member, console, _console),
	new(_dialog, dialog('Goal')),
	send(_dialog, append, new(_goal, text_item('Enter a new goal:'))),
	(fasiller_goal(X), send(_goal, selection, X) ; true),
	send(_dialog, append, new(button(accept, and(
		message(_console, Method, _goal?selection),
		message(_dialog, destroy)
	)))),
	send(_dialog, append, new(button(cancel, message(_dialog, destroy)))),
    send(_dialog, open).
	
:- pce_end_class(floper).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                  %%
%% INICIAR ENTORNO                                                  %%
%%                                                                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Crea la ventana principal del entorno
:- new(_floper, floper), send(_floper, open_centered).
