package de.intranda.utils;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.NotSerializableException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.UnsupportedEncodingException;
import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Logger;
import org.jdom.Document;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.jdom.output.Format;
import org.jdom.output.XMLOutputter;

/**
 * Collection of common all-purpose functions
 * 
 * 
 * @author florian
 * 
 */
public class CommonUtils {

	/** Logger for this class. */
	private static final Logger logger = Logger.getLogger(CommonUtils.class);
	private static final String encoding = "utf-8";

	/**
	 * Writing serializable objects to a file
	 * 
	 * @param file
	 * @param obj
	 */
	public static void writeFile(File file, Object obj) {
		try {
			FileOutputStream fs = new FileOutputStream(file);
			ObjectOutputStream os = new ObjectOutputStream(fs);
			os.writeObject(obj);
			os.close();
		} catch (IOException e) {
			logger.error("Error writing binary file", e);
		}
	}

	/**
	 * Reading serializable objects from a file
	 * 
	 * @param file
	 * @return
	 */
	public static Object readFile(File file) {
		FileInputStream fis;
		Object obj = null;
		try {
			fis = new FileInputStream(file);
			ObjectInputStream ois = new ObjectInputStream(fis);
			obj = ois.readObject();
			ois.close();
		} catch (FileNotFoundException e) {
			logger.warn("No binary file exists to read. Aborting.");
		} catch (IOException e) {
			logger.error("Error reading binary file", e);
		} catch (ClassNotFoundException e) {
			logger.error("Error reading object from binary file", e);
		}
		return obj;
	}

	/**
	 * Read a text file and return content as String
	 * 
	 * @param file
	 * @return
	 */
	public static String readTextFile(File file) {
		String result = "";
		FileReader fileReader = null;
		BufferedReader reader = null;

		try {
			fileReader = new FileReader(file);
			reader = new BufferedReader(fileReader);

			String zeile = null;

			while ((zeile = reader.readLine()) != null) {
				// logger.debug("Reading line: " + zeile);
				result = result.concat(zeile + "\n");
			}
		} catch (FileNotFoundException e) {
			logger.error(e.toString(), e);
			return null;
		} catch (IOException e) {
			logger.error(e.toString(), e);
			return null;
		} finally {
			try {
				if (reader != null)
					reader.close();
			} catch (IOException e) {
				System.err.println("ERROR: " + e.toString());
			}
		}
		return result.trim();
	}

	/**
	 * Simply write a String into a text file
	 * 
	 * @param string
	 * @param file
	 * @return
	 * @throws IOException
	 */
	public static File writeTextFile(String string, File file) throws IOException {

		FileWriter writer = null;
		writer = new FileWriter(file);
		writer.write(string);
		if (writer != null)
			writer.close();

		return file;
	}

	/**
	 * Writes the Document doc into an xml File file
	 * 
	 * @param file
	 * @param doc
	 * @throws IOException
	 */
	public static void getFileFromDocument(File file, Document doc) throws IOException {
		writeTextFile(getStringFromDocument(doc, encoding), file);
	}

	/**
	 * 
	 * Creates a single String out of the Document document
	 * 
	 * @param document
	 * @param encoding
	 * @return
	 */
	public static String getStringFromDocument(Document document, String encoding) {
		if (document == null) {
			logger.warn("Trying to convert null document to String. Aborting");
			return null;
		}
		XMLOutputter outputter = new XMLOutputter();
		Format xmlFormat = outputter.getFormat();
		if (!(encoding == null) && !encoding.isEmpty())
			xmlFormat.setEncoding(encoding);
		xmlFormat.setExpandEmptyElements(true);
		outputter.setFormat(xmlFormat);
		String docString = outputter.outputString(document);

		return docString;
	}

	/**
	 * Load a jDOM document from an xml file
	 * 
	 * @param file
	 * @return
	 */
	public static Document getDocumentFromFile(File file) {
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		try {
			document = builder.build(file);
		} catch (JDOMException e) {
			logger.error(e.toString(), e);
			return null;
		} catch (IOException e) {
			logger.error(e.toString(), e);
			return null;
		}
		return document;
	}

	/**
	 * Create a jDOM document from an xml string
	 * 
	 * @param string
	 * @return
	 */
	public static Document getDocumentFromString(String string) {
		byte[] byteArray = null;
		try {
			byteArray = string.getBytes(encoding);
		} catch (UnsupportedEncodingException e1) {
		}
		ByteArrayInputStream baos = new ByteArrayInputStream(byteArray);

		// Reader reader = new StringReader(hOCRText);
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		try {
			document = builder.build(baos);
		} catch (JDOMException e) {
			System.err.println("error " + e.toString());
			return null;
		} catch (IOException e) {
			System.err.println(e.toString());
			return null;
		}
		return document;
	}

	// Deletes all files and subdirectories under dir.
	// Returns true if all deletions were successful.
	// If a deletion fails, the method stops attempting to delete and returns false.
	public static boolean deleteDir(File dir) {
		if (dir.isDirectory()) {
			String[] children = dir.list();
			for (int i = 0; i < children.length; i++) {
				boolean success = deleteDir(new File(dir, children[i]));
				if (!success) {
					return false;
				}
			}
		}

		// The directory is now empty so delete it
		return dir.delete();
	}

	public static Object getFromMap(Map<String, ? extends Object> map, String id) {
		for (Object obj : map.keySet()) {
			if (obj instanceof String) {
				String key = (String) obj;
				if (id.contentEquals(key)) {
					return map.get(obj);
				}
			}
		}
		return null;
	}

}
