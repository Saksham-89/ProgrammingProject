package ProgrammingProject;

public class Move {
    private int field;

    public Move(int field) {
        this.field = field;
    }

    public int getField() {
        return field;
    }

    @Override
    public String toString() {
        return "Move to field " + field;
    }
}

