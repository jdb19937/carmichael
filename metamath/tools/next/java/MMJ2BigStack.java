/* Launcher for mmj2 with a large thread stack (sortie G5, TOOLING-DEBT
 * item 2, A5-HANDOFF open problem 1).  mmj2's proof assistant recurses on
 * the parse tree of every formula (mmj.lang.ParseNode.convertToRPNExpanded)
 * and overflows the JVM's primordial thread stack on a worksheet carrying
 * 2,000-token formulas; -Xss does not apply to that thread.  This class runs
 * mmj.util.BatchMMJ2.main on a fresh thread whose stack size is the system
 * property mmj2.stack (bytes, default 1 GiB) and exits with mmj2's status.
 *
 *   javac -cp mmj2.jar -d tools/java tools/java/MMJ2BigStack.java
 *   java -Djava.awt.headless=true -Xmx4g -Dmmj2.stack=1073741824 \
 *        -cp mmj2.jar:tools/java MMJ2BigStack RunParms.txt n
 *
 * tools/mm.py builds that command when the class file is present.
 */
public class MMJ2BigStack {
    public static void main(final String[] args) throws Throwable {
        long stack = Long.parseLong(System.getProperty("mmj2.stack", String.valueOf(1L << 30)));
        final Throwable[] err = new Throwable[1];
        Thread t = new Thread(null, new Runnable() {
            public void run() {
                try {
                    mmj.util.BatchMMJ2.main(args);
                } catch (Throwable e) {
                    err[0] = e;
                }
            }
        }, "main", stack);
        t.start();
        t.join();
        if (err[0] != null) {
            err[0].printStackTrace();
            System.exit(1);
        }
    }
}
