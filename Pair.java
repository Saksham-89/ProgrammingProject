package ProgrammingProject;

public class Pair {
    private int first;
    private int second;

    public Pair(int first, int second) {
        this.first = first;
        this.second = second;
    }

    public int getFirst() {
        return first;
    }

    public int getSecond() {
        return second;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Pair pair = (Pair) obj;
        return (first == pair.first && second == pair.second) || (first == pair.second && second == pair.first);
    }

    @Override
    public int hashCode() {
        return 31 * Math.min(first, second) + Math.max(first, second);
    }
}
