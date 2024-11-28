import threading
import tkinter as tk
from tkinter import filedialog, scrolledtext, messagebox
import re
from z3 import *
from pathlib import Path
from timeit import default_timer as timer

class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.room_capacities = []
        self.exams_to_students = []
        self.student_exam_capacity = []

# read file function 
def read_file(filename):
    instance = Instance()
    with open(filename) as f:
        def read_attribute(name):
            line = f.readline()
            match = re.match(f'{name}:\\s*(\\d+)$', line)
            if match:
                return int(match.group(1))
            else:
                raise ValueError(f"Could not parse line {line}; expected the {name} attribute")

        instance.number_of_students = read_attribute("Number of students")
        instance.number_of_exams = read_attribute("Number of exams")
        instance.number_of_slots = read_attribute("Number of slots")
        instance.number_of_rooms = read_attribute("Number of rooms")

        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))

        while True:
            line = f.readline()
            if line == "":
                break
            match = re.match('^\\s*(\\d+)\\s+(\\d+)\\s*$', line)
            if match:
                instance.exams_to_students.append((int(match.group(1)), int(match.group(2))))
            else:
                raise ValueError(f'Failed to parse this line: {line}')

        instance.student_exam_capacity = [0] * instance.number_of_exams
        for exam, student in instance.exams_to_students:
            instance.student_exam_capacity[exam] += 1

    return instance

def solve(instance):
    start_solve = timer()  # Timer for solving the instance

    s = Solver()

    # Variable Declarations
    exam = Int('exam')
    room = Int('room')
    timeslot = Int('timeslot')
    next_exam = Int('next_exam')
    next_timeslot = Int('next_timeslot')
    student = Int('student')

    # Range Functions for Constraints
    Student_Range = Function('Student_Range', IntSort(), BoolSort())
    Exam_Range = Function('Exam_Range', IntSort(), BoolSort())
    Room_Range = Function('Room_Range', IntSort(), BoolSort())
    TimeSlot_Range = Function('TimeSlot_Range', IntSort(), BoolSort())
    RoomCapacity = Function('RoomCapacity', IntSort(), IntSort())
    StudentCount = Function('StudentCount', IntSort(), IntSort())
    next_room = Int('next_room')

    # Matrix to track which invigilators are assigned to each exam and timeslot
    InvigilatorAssigned = [[[Bool(f"invig_{i}_exam_{e}_slot_{t}") for t in range(instance.number_of_slots)] for e in range(instance.number_of_exams)] for i in range(10)]

    # Range Constraints
    s.add(ForAll([student], Student_Range(student) == And(student >= 0, student < instance.number_of_students)))
    s.add(ForAll([exam], Exam_Range(exam) == And(exam >= 0, exam < instance.number_of_exams)))
    s.add(ForAll([timeslot], TimeSlot_Range(timeslot) == And(timeslot >= 0, timeslot < instance.number_of_slots)))
    s.add(ForAll([room], Room_Range(room) == And(room >= 0, room < instance.number_of_rooms)))

    # Functions for Exam Room, Time, and Students
    ExamRoom = Function('ExamRoom', IntSort(), IntSort())      # Maps each exam to a room
    ExamTime = Function('ExamTime', IntSort(), IntSort())      # Maps each exam to a timeslot
    ExamStudent = Function('ExamStudent', IntSort(), IntSort(), BoolSort())  # Indicates if a student is taking an exam

    # Add Students Taking Exams based on Input Data
    for exam_id, student_id in instance.exams_to_students:
        s.add(ExamStudent(exam_id, student_id))

    # Constraint 1 and 2: Room and Time Assignments for Exams
    s.add(
        ForAll(
            [exam],
            Implies(
                Exam_Range(exam),
                Exists(
                    [room, timeslot],
                    And(
                        Room_Range(room),
                        TimeSlot_Range(timeslot),
                        ExamTime(exam) == timeslot,
                        ExamRoom(exam) == room,
                        ForAll(
                            [next_exam],
                            Implies(
                                Exam_Range(next_exam),
                                Implies(
                                    And(
                                        ExamRoom(next_exam) == room,
                                        ExamTime(next_exam) == timeslot
                                    ),
                                    exam == next_exam
                                )
                            )
                        )
                    )
                )
            )
        )
    )

    # Constraint 3: Room Capacity
    for ex in range(instance.number_of_exams):
        for rm in range(instance.number_of_rooms):
            s.add(Implies(ExamRoom(ex) == rm, instance.student_exam_capacity[ex] <= instance.room_capacities[rm]))

    # Constraint 4: Non-overlapping Exams for Students
    s.add(
        ForAll([student, exam, next_exam, timeslot, next_timeslot],
               Implies(
                   And(
                       Student_Range(student),
                       Exam_Range(exam),
                       Exam_Range(next_exam),
                       TimeSlot_Range(timeslot),
                       TimeSlot_Range(next_timeslot),
                       exam != next_exam
                   ),
                   Implies(
                       And(
                           ExamTime(exam) == timeslot,
                           ExamTime(next_exam) == next_timeslot,
                           ExamStudent(exam, student),
                           ExamStudent(next_exam, student)
                       ),
                       And(timeslot + 1 != next_timeslot, timeslot - 1 != next_timeslot, timeslot != next_timeslot)  # Ensure no adjacent time slots for same student
                   )
               )
        )
    )

    # Constraint 5: Assign invigilators based on number of students and ensure no invigilator is invigilating for two consecutive time slots
    for e in range(instance.number_of_exams):
        students = instance.student_exam_capacity[e]
        invigilators_needed = If(students <= 10, 1, If(students <= 20, 2, 3))
        for t in range(instance.number_of_slots):
            s.add(Sum([InvigilatorAssigned[i][e][t] for i in range(10)]) == If(ExamTime(e) == t, invigilators_needed, 0))

    # Constraint 6:Total invigilators per time slot must not exceed 10
    for t in range(instance.number_of_slots):
        s.add(Sum([InvigilatorAssigned[i][e][t] for i in range(10) for e in range(instance.number_of_exams)]) <= 10)

    # Constraint 7: Each invigilator can only invigilate at most 2 exams
    for i in range(10):  # Loop over all invigilators
        s.add(Sum([If(Or([InvigilatorAssigned[i][e][t] for t in range(instance.number_of_slots)]), 1, 0) for e in range(instance.number_of_exams)]) <= 2)

    # Constraint 8: No invigilator can invigilate in consecutive time slots
    for i in range(10):
        for t1 in range(instance.number_of_slots - 1):
            s.add(Sum([InvigilatorAssigned[i][e][t1] + InvigilatorAssigned[i][e][t1 + 1] for e in range(instance.number_of_exams)]) <= 1)

    # Add mappings for room capacities and student counts using Z3 functions
    for rm in range(instance.number_of_rooms):
        s.add(RoomCapacity(rm) == instance.room_capacities[rm])
    for ex in range(instance.number_of_exams):
        s.add(StudentCount(ex) == instance.student_exam_capacity[ex])

    # Sort exams by the number of students in ascending order
    sorted_exams = sorted(range(instance.number_of_exams), key=lambda ex: instance.student_exam_capacity[ex])

    # Constraint 9: Optimal Room Allocation with Prioritization of Smallest Fit
    for ex in sorted_exams:
        s.add(
            Exists([room],
                And(
                    Room_Range(room),
                    ExamRoom(ex) == room,
                    RoomCapacity(room) >= StudentCount(ex),
                    # Ensure that no smaller room can also fit the exam
                    ForAll([next_room],
                            Implies(
                                And(
                                    Room_Range(next_room),
                                    next_room != room,
                                    RoomCapacity(next_room) >= StudentCount(ex)
                                ),
                                RoomCapacity(room) <= RoomCapacity(next_room)
                            )
                    )
                )
            )
        )

    output = ""
    if s.check() == sat:
        students_with_many_exams = []
        m = s.model()  # Only get the model when satisfiable
        output += 'Satisfied\n'
        output += "――――――――――――Exam Timetable――――――――――――--\n"
        for ex in range(instance.number_of_exams):
            room = m.eval(ExamRoom(ex))
            slot = m.eval(ExamTime(ex))
            students_count = instance.student_exam_capacity[ex]
            invigilators = sum([1 for i in range(10) if any(is_true(m.eval(InvigilatorAssigned[i][ex][t])) for t in range(instance.number_of_slots))])
            output += f"Exam: {ex} | Room: {room} | Slot: {slot} | Students: {students_count} | Invigilators: {invigilators}\n"
        output += "――――――――――――――――――――――――----------------\n"
        output += "Individual Timetables (Exam no, Slot, Room):\n"
        for student_id in range(instance.number_of_students):
            exams_for_student = [(exam, m.eval(ExamTime(exam)), m.eval(ExamRoom(exam))) for exam, stud in instance.exams_to_students if stud == student_id]
            if exams_for_student:
                exams_formatted = " | ".join(f"({ex}, {slot}, {room})" for ex, slot, room in exams_for_student)
                output += f"Student {student_id}: {exams_formatted}\n"

                # Track students with more than 3 exams
                if len(exams_for_student) > 3:
                     students_with_many_exams.append(student_id)
                     
            else:
                output += f"Student {student_id}: Student is not scheduled for any exam, please check with the student office.\n"


        if students_with_many_exams:
                output += "\n――――――――――――Warning――――――――――――\n"
                output += "Students with more than 3 exams: " + ", ".join(f"{id}" for id in students_with_many_exams) + ". " + "Please make sure they are not overwhelmed by the exams!" + "\n\n"

        # Invigilator Timetable (Only list exams without detailed info)
        output += "\nInvigilator Timetable:\n"
        for i in range(10): 
            assigned_exams = [e for e in range(instance.number_of_exams) if any(is_true(m.eval(InvigilatorAssigned[i][e][t])) for t in range(instance.number_of_slots))]
            if assigned_exams:
                output += f"Invigilator {i}: " + ", ".join(f"Exam {e}" for e in assigned_exams) + "\n"
            else:
                output += f"Invigilator {i}: No assigned exams.\n"
    else:
        output += 'Unsatisfied\n'
        
    end_solve = timer()  # Timer ends after solving the instance
    output += f"Time taken to solve the instance: {((end_solve - start_solve) * 1000):.2f} ms\n"
    return output

class SolverThread(threading.Thread):
    def __init__(self, files, callback):
        super().__init__()
        self.files = files
        self.callback = callback

    def run(self):
        for file in self.files:
            try:
                instance = read_file(file)
                results = solve(instance)
                self.callback(f"Results for {file}:\n{results}\n")
            except Exception as e:
                self.callback(f"Error processing {file}: {str(e)}\n")

def run_solver(files, callback):
    thread = SolverThread(files, callback)
    thread.start()

#function to generate txt files
def generate_txt(output):
    """
    Save the combined output for all instances into a .txt file.
    """
    if not output.strip():  # Check if output is empty
        messagebox.showwarning("Warning", "No data to save!")
        return

    # Prompt the user to select a save location
    file_path = filedialog.asksaveasfilename(
        defaultextension=".txt",
        filetypes=[("Text files", "*.txt")],
        title="Save Output as TXT"
    )
    if not file_path:  # If the user cancels, do nothing
        return

    try:
        # Write the combined output text to the specified file
        with open(file_path, 'w', encoding='utf-8') as txt_file:
            txt_file.write(output)

        # Display success message
        messagebox.showinfo("Success", "TXT file generated successfully!")
    except Exception as e:
        # Display error message in case of failure
        messagebox.showerror("Error", f"Failed to generate TXT file: {str(e)}")

    
def clear_text(result_text_widget):
    """Clears the displayed text in the result_text widget."""
    result_text_widget.config(state='normal')
    result_text_widget.delete(1.0, tk.END)  # Delete all text from the ScrolledText widget
    result_text_widget.config(state='disabled')

def create_gui():
    root = tk.Tk()
    root.title("Exam and Invigilator Scheduler")
    root.geometry("1200x900")  

    # Header Section
    header_frame = tk.Frame(root, pady=10)
    header_frame.pack(fill=tk.X)

    heading_label = tk.Label(header_frame, text="Exam Scheduler", font=("Arial", 24, "bold"))
    heading_label.pack()

    # Main Frame for scrollable content
    main_frame = tk.Frame(root, padx=10, pady=10)
    main_frame.pack(fill=tk.BOTH, expand=True)

    canvas = tk.Canvas(main_frame)
    scrollbar = tk.Scrollbar(main_frame, orient="vertical", command=canvas.yview)
    scrollable_frame = tk.Frame(canvas)

    scrollable_frame.bind(
        "<Configure>",
        lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
    )

    canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)

    canvas.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")

    def add_output_section(filename, sat_status, time_taken, exam_output=None, student_output=None, invigilator_output=None, warning_output=None):
        # Section Frame
        section_frame = tk.Frame(scrollable_frame, pady=10, padx=10, relief=tk.RIDGE, bd=2)
        section_frame.pack(fill=tk.BOTH, expand=True, pady=10)

        # File and SAT/UNSAT status
        status_label = tk.Label(section_frame, text=f"File: {filename} | Status: {sat_status}", font=("Arial", 12, "bold"))
        status_label.pack(anchor="w", pady=(5, 0))

        # Time Taken
        time_label = tk.Label(section_frame, text=f"Time taken to solve the instance: {time_taken}", font=("Arial", 12))
        time_label.pack(anchor="w", pady=(0, 5))

        # Warning Message (if any)
        if warning_output:  # Display warning if present
            warning_label = tk.Label(section_frame, text=f"!! Warning !!\n{warning_output}", font=("Arial", 12), fg="red")
            warning_label.pack(anchor="w", pady=(0, 10))

        if sat_status == "SAT":  # Only display timetables for SAT instances
            # Timetables
            timetable_frame = tk.Frame(section_frame)
            timetable_frame.pack(fill=tk.BOTH, expand=True)

            # Exam Timetable Section
            if exam_output:  # Only display if exam timetable exists
                exam_frame = tk.LabelFrame(timetable_frame, text="Exam Timetable", font=("Arial", 12, "bold"))
                exam_frame.grid(row=0, column=0, padx=5, pady=5, sticky="nsew")
                exam_text = scrolledtext.ScrolledText(exam_frame, height=10, wrap=tk.WORD, state='normal', font=("Courier", 10))
                exam_text.insert(tk.END, exam_output)
                exam_text.config(state='disabled')
                exam_text.pack(fill=tk.BOTH, expand=True)

            # Student Timetable Section
            if student_output:  # Ensure exam details are excluded from this section
                student_frame = tk.LabelFrame(timetable_frame, text="Student Timetable (Exam, Slot, Room)", font=("Arial", 12, "bold"))
                student_frame.grid(row=0, column=1, padx=5, pady=5, sticky="nsew")
                student_text = scrolledtext.ScrolledText(student_frame, height=10, wrap=tk.WORD, state='normal', font=("Courier", 10))
                # Filter out any lines that include "Exam:" (exam timetable details)
                filtered_student_output = "\n".join(
                    line for line in student_output.splitlines() if not line.startswith("Exam:")
                )
                student_text.insert(tk.END, filtered_student_output or "No data available")
                student_text.config(state='disabled')
                student_text.pack(fill=tk.BOTH, expand=True)

            # Invigilator Timetable Section
            if invigilator_output:  # Ensure exam details are excluded from this section
                invigilator_frame = tk.LabelFrame(timetable_frame, text="Invigilator Timetable", font=("Arial", 12, "bold"))
                invigilator_frame.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky="nsew")
                invigilator_text = scrolledtext.ScrolledText(invigilator_frame, height=10, wrap=tk.WORD, state='normal', font=("Courier", 10))
                # Filter out any lines that include "Exam:" (exam timetable details)
                filtered_invigilator_output = "\n".join(
                    line for line in invigilator_output.splitlines() if not line.startswith("Exam:")
                )
                invigilator_text.insert(tk.END, filtered_invigilator_output or "No data available")
                invigilator_text.config(state='disabled')
                invigilator_text.pack(fill=tk.BOTH, expand=True)

            # Adjust Grid
            timetable_frame.grid_columnconfigure(0, weight=1)
            timetable_frame.grid_columnconfigure(1, weight=1)


    # Function to handle results and add them to the GUI
    def handle_results(filename, results):
        # Parse the output into its components (SAT/UNSAT status, time, and timetables)
        sat_status = "SAT" if "Satisfied" in results else "UNSAT"
        time_taken_match = re.search(r"Time taken to solve the instance: (\d+\.\d+) ms", results) 
        time_taken = f"{float(time_taken_match.group(1)):.2f} ms" if time_taken_match else "N/A"

        # Only parse timetables if SAT
        exam_output = "\n".join(line for line in results.splitlines() if "Exam:" in line) if sat_status == "SAT" else None
        invigilator_output = "\n".join(line for line in results.splitlines() if "Invigilator" in line) if sat_status == "SAT" else None
        # Extract the student timetable while excluding warning lines
        student_output = "\n".join(
            line for line in results.splitlines() 
            if "Student" in line and not line.startswith("Students with more than")
        ) if sat_status == "SAT" else None

        # Extract warning messages separately
        warning_output = next(
            (line for line in results.splitlines() if "Students with more than" in line), 
            None
        )


        # Add output to the GUI
        add_output_section(filename, sat_status, time_taken, exam_output, student_output, invigilator_output, warning_output)

    def run_solver_instance(files):
        global current_output  # Store the combined output for all instances
        current_output = ""  # Reset current_output before solving all instances

        for file in files:
            try:
                instance = read_file(file)
                results = solve(instance)  # Get the output for the current instance
                current_output += f"Results for {file}:\n{results}\n{'-' * 80}\n"  # Append results for each instance
                handle_results(file, results)  # Display results in the GUI
            except Exception as e:
                current_output += f"Error processing {file}: {e}\n{'-' * 80}\n"
                handle_results(file, f"Error processing {file}: {e}")

    # Buttons Section
    button_frame = tk.Frame(root, pady=10)
    button_frame.pack(fill=tk.X)

    # Clear all output in the scrollable frame
    def clear_all(scrollable_frame):
        """Clears all widgets from the scrollable frame."""
        for widget in scrollable_frame.winfo_children():
            widget.destroy()  # Remove all child widgets from the scrollable frame

    # Buttons Section (Above Title)
    button_frame_top = tk.Frame(header_frame, pady=10)
    button_frame_top.pack(side=tk.TOP, pady=10)

    run_all_button = tk.Button(
        button_frame_top,
        text="Run All Instances",
        font=("Arial", 14, "bold"),
        width=18,
        height=2,
        command=lambda: run_solver_instance(list(Path("./test instances").glob("*.txt"))),
    )
    run_all_button.pack(side=tk.LEFT, padx=10)

    open_file_button = tk.Button(
        button_frame_top,
        text="Select File and Run",
        font=("Arial", 14, "bold"),
        width=18,
        height=2,
        command=lambda: run_solver_instance([filedialog.askopenfilename()]),
    )
    open_file_button.pack(side=tk.LEFT, padx=10)

    clear_button = tk.Button(
        button_frame_top,
        text="Clear All",
        font=("Arial", 14, "bold"),
        width=18,
        height=2,
        command=lambda: clear_all(scrollable_frame),
    )
    clear_button.pack(side=tk.LEFT, padx=10)

    generate_txt_button = tk.Button(
    button_frame_top,
    text="Generate TXT",
    font=("Arial", 14, "bold"),
    width=18,
    height=2,
    command=lambda: generate_txt(current_output),  # Use the combined output
)
    generate_txt_button.pack(side=tk.LEFT, padx=10)

    root.mainloop()


if __name__ == "__main__":
    create_gui()


