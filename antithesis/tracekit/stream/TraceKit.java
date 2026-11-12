import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.Map;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * TLC override for module TraceKit: StreamEvent(i) is the i-th line of a
 * growing ndjson file, as a TLA+ record. It blocks until that line has been
 * written, so a breadth-first search with one worker advances in step with
 * whatever appends to the file.
 *
 * TRACE_STREAM names the file. When "<file>.eof" exists and line i does not,
 * the stream has ended and StreamEvent(i) is [e |-> "End"].
 * TRACE_PROGRESS, if set, names a file that always holds the highest index
 * requested so far: every earlier event has been matched by the model.
 *
 * Nothing here knows what the events mean.
 */
public class TraceKit {
    private static final int KEEP = 4096;
    private static final ArrayDeque<Value> window = new ArrayDeque<>();
    private static int first = 1;          // index of window's first element
    private static RandomAccessFile file;
    private static final byte[] buf = new byte[1 << 16];
    private static int pos = 0;
    private static int len = 0;
    private static final java.io.ByteArrayOutputStream line = new java.io.ByteArrayOutputStream();
    private static int highest = 0;
    private static final Value END = record(new String[] {"e"}, new Value[] {new StringValue("End")});

    public static synchronized Value StreamEvent(final IntValue idx) throws IOException, InterruptedException {
        final int i = idx.val;
        if (i < first) {
            throw new IllegalStateException("TraceKit: event " + i + " is no longer buffered");
        }
        if (i > highest) {
            highest = i;
            progress(i);
        }
        final String path = System.getenv("TRACE_STREAM");
        // Read only as far as event i: the reader must not run ahead of the
        // search, or events the search still needs would leave the window.
        while (first + window.size() <= i) {
            if (file == null) {
                final File f = new File(path);
                if (f.exists()) {
                    file = new RandomAccessFile(f, "r");
                }
            }
            if (file != null && readLine()) {
                continue;
            }
            if (new File(path + ".eof").exists() && (file == null || !readLine())) {
                return END;
            }
            Thread.sleep(2);
        }
        int k = first;
        for (Value v : window) {
            if (k == i) {
                return v;
            }
            k++;
        }
        throw new IllegalStateException("TraceKit: event " + i + " not in window");
    }

    /** Appends the next whole line to the window; false if there is none yet. */
    private static boolean readLine() throws IOException {
        while (true) {
            while (pos < len) {
                final byte c = buf[pos++];
                if (c != '\n') {
                    line.write(c);
                    continue;
                }
                final String s = new String(line.toByteArray(), StandardCharsets.UTF_8);
                line.reset();
                if (s.isBlank()) {
                    continue;
                }
                window.addLast(toValue(JsonParser.parseString(s)));
                while (window.size() > KEEP) {
                    window.removeFirst();
                    first++;
                }
                return true;
            }
            final int n = file.read(buf);
            if (n <= 0) {
                return false;
            }
            pos = 0;
            len = n;
        }
    }

    private static void progress(final int i) {
        final String p = System.getenv("TRACE_PROGRESS");
        if (p == null) {
            return;
        }
        try (FileWriter w = new FileWriter(p + ".tmp")) {
            w.write(Integer.toString(i));
        } catch (IOException e) {
            return;
        }
        new File(p + ".tmp").renameTo(new File(p));
    }

    private static Value record(final String[] names, final Value[] values) {
        final UniqueString[] u = new UniqueString[names.length];
        for (int j = 0; j < names.length; j++) {
            u[j] = UniqueString.uniqueStringOf(names[j]);
        }
        return new RecordValue(u, values, false);
    }

    private static Value toValue(final JsonElement e) {
        if (e.isJsonObject()) {
            final JsonObject o = e.getAsJsonObject();
            final String[] names = new String[o.size()];
            final Value[] values = new Value[o.size()];
            int j = 0;
            for (Map.Entry<String, JsonElement> m : o.entrySet()) {
                names[j] = m.getKey();
                values[j] = toValue(m.getValue());
                j++;
            }
            return record(names, values);
        }
        if (e.isJsonArray()) {
            final JsonArray a = e.getAsJsonArray();
            final Value[] values = new Value[a.size()];
            for (int j = 0; j < values.length; j++) {
                values[j] = toValue(a.get(j));
            }
            return new TupleValue(values);
        }
        if (e.isJsonPrimitive()) {
            final JsonPrimitive p = e.getAsJsonPrimitive();
            if (p.isBoolean()) {
                return p.getAsBoolean() ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            if (p.isNumber()) {
                return IntValue.gen(p.getAsInt());
            }
            return new StringValue(p.getAsString());
        }
        return new StringValue("");
    }
}
